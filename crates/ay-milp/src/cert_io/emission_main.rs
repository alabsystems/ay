// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

pub(super) struct Emission<'ctx, 'model> {
    pub(super) ctx: &'ctx EmitCtx<'model>,
    pub(super) claims: Vec<EmittedClaim>,
    pub(super) blocks: String,
    pub(super) extras: String,
    pub(super) truncated: Vec<String>,
    pub(super) affine_emitted: bool,
}

impl<'ctx, 'model> Emission<'ctx, 'model> {
    fn new(ctx: &'ctx EmitCtx<'model>) -> Self {
        Self {
            ctx,
            claims: Vec::new(),
            blocks: String::new(),
            extras: String::new(),
            truncated: Vec::new(),
            affine_emitted: false,
        }
    }

    pub(super) fn admit(&mut self, body: String, what: &str) -> bool {
        if let Some(cap) = self.ctx.max_bytes {
            if self
                .blocks
                .len()
                .checked_add(body.len())
                .is_none_or(|total| total > cap)
            {
                self.truncated
                    .push(format!("truncated {what} bytes={} cap={cap}", body.len()));
                return false;
            }
        }
        self.blocks.push_str(&body);
        true
    }

    pub(super) fn block_claim(
        &mut self,
        name: &'static str,
        body: String,
        what: &str,
        source: &str,
    ) -> EmittedClaim {
        let admitted = self.admit(body, what);
        EmittedClaim {
            name,
            kind: if admitted {
                EvidenceKind::Succinct
            } else {
                EvidenceKind::None
            },
            source: Some(if admitted { source } else { "truncated" }.into()),
        }
    }

    pub(super) fn codec_claim(
        &mut self,
        name: &'static str,
        body: Option<String>,
        what: &str,
        source: &str,
    ) -> EmittedClaim {
        let Some(body) = body else {
            self.truncated
                .push(format!("truncated {what} bytes=unavailable cap=codec"));
            return EmittedClaim {
                name,
                kind: EvidenceKind::None,
                source: Some("truncated".into()),
            };
        };
        self.block_claim(name, body, what, source)
    }

    pub(super) fn affine_claim(
        &mut self,
        name: &'static str,
        certificate: &AffineAggregationCertificate,
    ) -> EmittedClaim {
        let limit = self.ctx.max_bytes.map_or(MAX_AFFINE_WIRE_BYTES, |cap| {
            cap.saturating_sub(self.blocks.len())
        });
        let body = affine_aggregation_block(certificate, limit);
        let claim = self.codec_claim(name, body, "affine-aggregation", "affine-aggregation");
        self.affine_emitted = true;
        claim
    }
}

/// Serialize an outcome as a `.ayc` certificate.
///
/// Emission is total: every verdict produces a certificate, including those
/// for which this build has no independently checkable evidence.
#[must_use]
pub fn emit(ctx: &EmitCtx<'_>, outcome: &Outcome) -> String {
    let mut emission = Emission::new(ctx);
    let verdict = match outcome {
        Outcome::Optimal { .. } => emit_optimal(&mut emission, outcome),
        Outcome::Feasible { .. } => emit_feasible(&mut emission, outcome),
        Outcome::Infeasible { .. } => emit_infeasible(&mut emission, outcome),
        Outcome::Unbounded => emit_unbounded(&mut emission),
        Outcome::Bound { .. } => emit_bound(&mut emission, outcome),
        Outcome::Unknown { reason } => {
            let _ = writeln!(emission.extras, "reason {}", unknown_reason_line(reason));
            "verdict unknown".to_owned()
        }
    };
    emit_auxiliary_blocks(&mut emission);
    finish(emission, outcome, &verdict)
}

fn emit_feasible(emission: &mut Emission<'_, '_>, outcome: &Outcome) -> String {
    let Outcome::Feasible {
        model_values,
        incumbent_only,
        dual_bound,
    } = outcome
    else {
        return String::new();
    };
    let claim = emission.block_claim(
        "primal",
        witness_block(emission.ctx, model_values),
        "witness",
        "witness",
    );
    emission.claims.push(claim);
    if let Some(bound) = dual_bound {
        let _ = writeln!(
            emission.extras,
            "unchecked dual_bound={} frame=file",
            fmt_rat(&(bound / emission.ctx.obj_scale))
        );
    }
    emission.claims.push(EmittedClaim {
        name: "dual",
        kind: EvidenceKind::None,
        source: None,
    });
    let value = emission.ctx.model.objective_value_at(model_values);
    format!(
        "verdict feasible value={} frame=file incumbent_only={}",
        fmt_rat(&(&value / emission.ctx.obj_scale)),
        u8::from(*incumbent_only)
    )
}

fn emit_unbounded(emission: &mut Emission<'_, '_>) -> String {
    emission.claims.push(EmittedClaim {
        name: "unbounded",
        kind: EvidenceKind::None,
        source: None,
    });
    "verdict unbounded".to_owned()
}

fn emit_bound(emission: &mut Emission<'_, '_>, outcome: &Outcome) -> String {
    let Outcome::Bound {
        dual_bound,
        rigorous,
    } = outcome
    else {
        return String::new();
    };
    let _ = writeln!(
        emission.extras,
        "unchecked dual_bound={} frame=file rigorous={}",
        fmt_rat(&(dual_bound / emission.ctx.obj_scale)),
        u8::from(*rigorous)
    );
    emission.claims.push(EmittedClaim {
        name: "dual",
        kind: EvidenceKind::None,
        source: None,
    });
    "verdict bound".to_owned()
}

fn emit_auxiliary_blocks(emission: &mut Emission<'_, '_>) {
    if !emission.affine_emitted {
        if let Some(certificate) = emission.ctx.affine_aggregation_certificate {
            let limit = emission.ctx.max_bytes.map_or(MAX_AFFINE_WIRE_BYTES, |cap| {
                cap.saturating_sub(emission.blocks.len())
            });
            match affine_aggregation_block(certificate, limit) {
                Some(body) => {
                    let _ = emission.admit(body, "affine-aggregation");
                }
                None => emission
                    .truncated
                    .push("truncated affine-aggregation bytes=unavailable cap=codec".to_owned()),
            }
        }
    }
    for replay in emission.ctx.replay_claims {
        let _ = emission.admit(replay_block(replay), "replay");
    }
}

fn finish(emission: Emission<'_, '_>, outcome: &Outcome, verdict: &str) -> String {
    let ctx = emission.ctx;
    let mut out = String::new();
    let _ = writeln!(out, "%AYC {AYC_VERSION}");
    let _ = writeln!(
        out,
        "model file sha256:{} bytes={} form=text",
        sha256_hex(ctx.model_text.as_bytes()),
        ctx.model_text.len()
    );
    let _ = writeln!(
        out,
        "model canon v1 sha256:{}",
        emitted_model_canon_digest(ctx.model, outcome, ctx.sat_relu_infeasibility_certificate)
    );
    write_model_header(&mut out, ctx);
    let _ = writeln!(out, "{verdict}");
    for claim in &emission.claims {
        match &claim.source {
            Some(source) => {
                let _ = writeln!(
                    out,
                    "evidence {} {} {source}",
                    claim.name,
                    claim.kind.token()
                );
            }
            None => {
                let _ = writeln!(out, "evidence {} {}", claim.name, claim.kind.token());
            }
        }
    }
    out.push_str(&emission.extras);
    for line in &emission.truncated {
        let _ = writeln!(out, "{line}");
    }
    out.push_str(&emission.blocks);
    let digest = sha256_hex(out.as_bytes());
    let _ = writeln!(out, "%END sha256:{digest}");
    out
}

fn write_model_header(out: &mut String, ctx: &EmitCtx<'_>) {
    let intcols = (0..ctx.model.num_cols())
        .filter(|&column| ctx.model.col_kind(Col(column as u32)).is_integral())
        .count();
    let _ = writeln!(
        out,
        "model shape rows={} cols={} intcols={intcols} sense={} obj_scale={}",
        ctx.model.num_rows(),
        ctx.model.num_cols(),
        sense_token(ctx.model.sense()),
        fmt_rat(ctx.obj_scale)
    );
    let _ = writeln!(
        out,
        "solver ay-milp {} {}",
        env!("CARGO_PKG_VERSION"),
        sanitize(ctx.provenance)
    );
}
