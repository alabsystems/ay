// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

#![cfg(test)]

//! Frozen pre-control wire encoders; independent spelling/count/error oracle.
use super::*;

pub(super) fn encode_value(
    value: &SmtValue,
    expected_sort: &ChcSort,
    depth: usize,
    value_nodes: &mut usize,
) -> Result<WireValue, ChcGroundDerivationArtifactError> {
    validate_value_depth(depth)?;
    increment_count(
        value_nodes,
        CHC_GROUND_DERIVATION_ARTIFACT_MAX_VALUE_NODES,
        ChcGroundDerivationArtifactErrorReason::TooManyValueNodes,
        "value node",
    )?;

    match (value, expected_sort) {
        (SmtValue::Bool(value), ChcSort::Bool) => Ok(WireValue::Bool { value: *value }),
        (SmtValue::Int(value), ChcSort::Int) => Ok(WireValue::Int {
            decimal: value.to_string(),
        }),
        (SmtValue::BigInt(value), ChcSort::Int) => Ok(WireValue::Int {
            decimal: value.to_string(),
        }),
        (SmtValue::Real(value), ChcSort::Real) => Ok(WireValue::Real {
            numerator: value.numer().to_string(),
            denominator: value.denom().to_string(),
        }),
        (SmtValue::BitVec(_, width) | SmtValue::BigBitVec(_, width), ChcSort::BitVec(expected))
            if width == expected =>
        {
            let Some((value, canonical_width)) = value.bitvec_to_biguint() else {
                return Err(error(
                    ChcGroundDerivationArtifactErrorReason::InvalidValue,
                    "bitvector width is outside AY's public bound",
                ));
            };
            Ok(WireValue::Bitvector {
                width: canonical_width,
                value_hex: value.to_str_radix(16),
            })
        }
        (SmtValue::ConstArray(default), ChcSort::Array(index_sort, value_sort)) => {
            validate_array_index_sort(index_sort)?;
            Ok(WireValue::ConstArray {
                default: Box::new(encode_value(default, value_sort, depth + 1, value_nodes)?),
            })
        }
        (SmtValue::ArrayMap { default, entries }, ChcSort::Array(index_sort, value_sort)) => {
            validate_array_index_sort(index_sort)?;
            let default = Box::new(encode_value(default, value_sort, depth + 1, value_nodes)?);
            let entries = entries
                .iter()
                .map(|(index, value)| {
                    Ok(WireArrayEntry {
                        index: encode_value(index, index_sort, depth + 1, value_nodes)?,
                        value: encode_value(value, value_sort, depth + 1, value_nodes)?,
                    })
                })
                .collect::<Result<Vec<_>, ChcGroundDerivationArtifactError>>()?;
            Ok(WireValue::ArrayMap { default, entries })
        }
        (SmtValue::Datatype(constructor, fields), ChcSort::Datatype { constructors, .. }) => {
            validate_text_value(constructor, "datatype constructor")?;
            let Some(definition) = constructors
                .iter()
                .find(|definition| definition.name == *constructor)
            else {
                return Err(error(
                    ChcGroundDerivationArtifactErrorReason::BindingSortMismatch,
                    format!("datatype constructor `{constructor}` is not in the source sort"),
                ));
            };
            if fields.len() != definition.selectors.len() {
                return Err(error(
                    ChcGroundDerivationArtifactErrorReason::BindingSortMismatch,
                    format!(
                        "datatype constructor `{constructor}` has {} fields, expected {}",
                        fields.len(),
                        definition.selectors.len()
                    ),
                ));
            }
            let fields = fields
                .iter()
                .zip(&definition.selectors)
                .map(|(field, selector)| {
                    encode_value(field, &selector.sort, depth + 1, value_nodes)
                })
                .collect::<Result<Vec<_>, _>>()?;
            Ok(WireValue::Datatype {
                constructor: constructor.clone(),
                fields,
            })
        }
        (SmtValue::Opaque(_), _) => Err(error(
            ChcGroundDerivationArtifactErrorReason::OpaqueValue,
            "opaque solver placeholders are not concrete portable values",
        )),
        (_, ChcSort::Uninterpreted(name)) => Err(error(
            ChcGroundDerivationArtifactErrorReason::BindingSortMismatch,
            format!("uninterpreted sort `{name}` has no portable concrete value encoding"),
        )),
        _ => Err(error(
            ChcGroundDerivationArtifactErrorReason::BindingSortMismatch,
            format!("value {value:?} does not match source sort {expected_sort}"),
        )),
    }
}

pub(super) fn wire_steps_from_derivation(
    problem: &ChcProblem,
    derivation: &GroundDerivation,
) -> Result<(Vec<WireStep>, ContentCounts), ChcGroundDerivationArtifactError> {
    if derivation.steps.len() > CHC_GROUND_DERIVATION_ARTIFACT_MAX_STEPS {
        return Err(error(
            ChcGroundDerivationArtifactErrorReason::TooManySteps,
            format!(
                "derivation has {} steps, maximum is {}",
                derivation.steps.len(),
                CHC_GROUND_DERIVATION_ARTIFACT_MAX_STEPS
            ),
        ));
    }

    let clause_indices = derivation
        .steps
        .iter()
        .map(|step| step.clause_index)
        .collect::<Vec<_>>();
    let SourceSurfacePreflight {
        mut cache,
        binding_count,
        ..
    } = preflight_source_surfaces(problem, &clause_indices)?;
    preflight_derivation_scalar_work(&mut cache, derivation)?;
    let mut counts = ContentCounts {
        bindings: binding_count,
        ..ContentCounts::default()
    };
    for step in &derivation.steps {
        add_count(
            &mut counts.premise_edges,
            step.premises.len(),
            CHC_GROUND_DERIVATION_ARTIFACT_MAX_PREMISE_EDGES,
            ChcGroundDerivationArtifactErrorReason::TooManyPremiseEdges,
            "premise edge",
        )?;
    }
    let mut steps = Vec::with_capacity(derivation.steps.len());
    for (step_index, step) in derivation.steps.iter().enumerate() {
        for name in step.env.keys() {
            validate_text_value(name, "binding name")?;
            if name.starts_with('\0') {
                return Err(error(
                    ChcGroundDerivationArtifactErrorReason::UnsupportedUninterpretedFunction,
                    format!(
                        "step {step_index} contains a private UF observation; artifact v1 \
                         supports only ordinary source-variable bindings"
                    ),
                ));
            }
        }

        let variables = &cache
            .surface(step.clause_index)
            .map_err(|surface_error| {
                map_source_surface_error(step_index, step.clause_index, surface_error)
            })?
            .variables;
        if variables.len() != step.env.len() {
            return Err(error(
                ChcGroundDerivationArtifactErrorReason::BindingSetMismatch,
                format!(
                    "step {step_index} has {} bindings, source clause {} requires {}",
                    step.env.len(),
                    step.clause_index,
                    variables.len()
                ),
            ));
        }
        let bindings = variables
            .iter()
            .map(|variable| {
                let Some(value) = step.env.get(&variable.name) else {
                    return Err(error(
                        ChcGroundDerivationArtifactErrorReason::BindingSetMismatch,
                        format!(
                            "step {step_index} omits source variable `{}`",
                            variable.name
                        ),
                    ));
                };
                Ok(WireBinding {
                    name: variable.name.clone(),
                    value: encode_value(value, &variable.sort, 1, &mut counts.value_nodes)?,
                })
            })
            .collect::<Result<Vec<_>, ChcGroundDerivationArtifactError>>()?;
        let premises = step
            .premises
            .iter()
            .map(|premise| checked_u32(*premise, "premise index"))
            .collect::<Result<Vec<_>, _>>()?;
        steps.push(WireStep {
            clause_index: checked_u32(step.clause_index, "clause index")?,
            premises,
            bindings,
        });
    }
    Ok((steps, counts))
}

pub(super) fn wire_steps_v2_from_derivation(
    problem: &ChcProblem,
    derivation: &GroundDerivation,
) -> Result<(Vec<WireStepV2>, ContentCounts), ChcGroundDerivationArtifactError> {
    if derivation.steps.len() > CHC_GROUND_DERIVATION_ARTIFACT_MAX_STEPS {
        return Err(error(
            ChcGroundDerivationArtifactErrorReason::TooManySteps,
            format!(
                "derivation has {} steps, maximum is {}",
                derivation.steps.len(),
                CHC_GROUND_DERIVATION_ARTIFACT_MAX_STEPS
            ),
        ));
    }

    let clause_indices = derivation
        .steps
        .iter()
        .map(|step| step.clause_index)
        .collect::<Vec<_>>();
    let SourceSurfacePreflight {
        mut cache,
        binding_count,
        uf_observation_count,
    } = preflight_source_surfaces(problem, &clause_indices)?;
    preflight_derivation_scalar_work(&mut cache, derivation)?;
    let mut counts = ContentCounts {
        bindings: binding_count,
        uf_observations: uf_observation_count,
        ..ContentCounts::default()
    };
    for step in &derivation.steps {
        add_count(
            &mut counts.premise_edges,
            step.premises.len(),
            CHC_GROUND_DERIVATION_ARTIFACT_MAX_PREMISE_EDGES,
            ChcGroundDerivationArtifactErrorReason::TooManyPremiseEdges,
            "premise edge",
        )?;
    }
    let mut global_congruence = FxHashMap::default();
    let mut steps = Vec::with_capacity(derivation.steps.len());
    for (step_index, step) in derivation.steps.iter().enumerate() {
        let surface = cache.surface(step.clause_index).map_err(|surface_error| {
            map_source_surface_error(step_index, step.clause_index, surface_error)
        })?;
        let variables = &surface.variables;
        let applications = &surface.uf_applications;
        let variable_names: FxHashSet<&str> = variables
            .iter()
            .map(|variable| variable.name.as_str())
            .collect();
        for name in step.env.keys() {
            validate_text_value(name, "binding name")?;
            if !variable_names.contains(name.as_str()) && !private_uf_model_key(name) {
                return Err(error(
                    ChcGroundDerivationArtifactErrorReason::BindingSetMismatch,
                    format!(
                        "step {step_index} environment entry `{name}` is neither a source variable nor finite-UF metadata"
                    ),
                ));
            }
        }
        let mut authenticated_env = FxHashMap::default();
        let bindings = variables
            .iter()
            .map(|variable| {
                let Some(value) = step.env.get(&variable.name) else {
                    return Err(error(
                        ChcGroundDerivationArtifactErrorReason::BindingSetMismatch,
                        format!(
                            "step {step_index} omits source variable `{}`",
                            variable.name
                        ),
                    ));
                };
                authenticated_env.insert(variable.name.clone(), value.clone());
                Ok(WireBinding {
                    name: variable.name.clone(),
                    value: encode_value(value, &variable.sort, 1, &mut counts.value_nodes)?,
                })
            })
            .collect::<Result<Vec<_>, ChcGroundDerivationArtifactError>>()?;

        let results = applications
            .iter()
            .enumerate()
            .map(|(application_index, application)| {
                eval_ground_pub(application, &step.env).ok_or_else(|| {
                    error(
                        ChcGroundDerivationArtifactErrorReason::UfObservationNotGround,
                        format!(
                            "step {step_index} application {application_index} has no exact source observation"
                        ),
                    )
                })
            })
            .collect::<Result<Vec<_>, ChcGroundDerivationArtifactError>>()?;
        install_authenticated_uf_observations(
            step_index,
            applications,
            &results,
            &mut authenticated_env,
            &mut global_congruence,
        )?;
        let uf_observations = applications
            .iter()
            .zip(&results)
            .enumerate()
            .map(|(application_index, (application, result))| {
                let ChcExpr::FuncApp(_, return_sort, _) = application else {
                    unreachable!("ordinary-UF collector returned a function application")
                };
                Ok(WireUfObservation {
                    application_ordinal: checked_u32(application_index, "UF application ordinal")?,
                    result: encode_value(result, return_sort, 1, &mut counts.value_nodes)?,
                })
            })
            .collect::<Result<Vec<_>, ChcGroundDerivationArtifactError>>()?;
        let premises = step
            .premises
            .iter()
            .map(|premise| checked_u32(*premise, "premise index"))
            .collect::<Result<Vec<_>, _>>()?;
        steps.push(WireStepV2 {
            clause_index: checked_u32(step.clause_index, "clause index")?,
            premises,
            bindings,
            uf_observations,
        });
    }
    Ok((steps, counts))
}
