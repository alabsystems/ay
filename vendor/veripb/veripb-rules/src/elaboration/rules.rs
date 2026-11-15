//! `Elaboratable` impls: each rule writes its own line(s) of the elaborated
//! proof. Rules that emit nothing use the default impl (bottom of file).

use veripb_formula::prelude::{ToPrettyString, VarNameLookup};

use crate::elaboration::{ConstraintLookup, Elaboratable, ElaborationError, Elaborator};
use crate::keywords::*;
use crate::prelude::*;
use itertools::Itertools;

impl Elaboratable for PreservedEqualsRule {
    fn elaborate<C: ConstraintLookup, V: VarNameLookup>(
        &self,
        elaborator: &mut Elaborator,
        _database: &C,
        var_lookup: &V,
    ) -> Result<(), ElaborationError> {
        elaborator.write("epreserved");
        elaborator.write(" ");
        elaborator.write(
            &self
                .vars
                .iter()
                .map(|v| v.to_pretty_string(var_lookup))
                .join(" "),
        );
        elaborator.writeln(";");
        Ok(())
    }
}

impl Elaboratable for OrderDefRule {
    fn elaborate<C: ConstraintLookup, V: VarNameLookup>(
        &self,
        elaborator: &mut Elaborator,
        _database: &C,
        _var_lookup: &V,
    ) -> Result<(), ElaborationError> {
        elaborator.write_indent();
        elaborator.writeln("def");
        elaborator.inc_indent();
        Ok(())
    }
}

impl Elaboratable for OrderAuxVariablesRule {
    fn elaborate<C: ConstraintLookup, V: VarNameLookup>(
        &self,
        elaborator: &mut Elaborator,
        _database: &C,
        var_lookup: &V,
    ) -> Result<(), ElaborationError> {
        elaborator.write_indented_var_list("aux", &self.vars, var_lookup);
        Ok(())
    }
}

impl Elaboratable for ImpliesRule {
    fn elaborate<C: ConstraintLookup, V: VarNameLookup>(
        &self,
        elaborator: &mut Elaborator,
        database: &C,
        var_lookup: &V,
    ) -> Result<(), ElaborationError> {
        if self.add_result {
            elaborator.write_indent();
            elaborator.write("ia");
            elaborator.write(" ");
            elaborator.write(&self.constraint.to_pretty_string(var_lookup));
            elaborator.write(" : ");
            let premise = database
                .get_entry_usize(self.hint.unwrap() as usize)
                .expect("constraint accessed before");
            elaborator.write(
                &premise
                    .get_out_id(premise.get_some_id())
                    .unwrap()
                    .to_string(),
            );
            elaborator.writeln(";");
        }
        Ok(())
    }
}

impl Elaboratable for OrderRightVariablesRule {
    fn elaborate<C: ConstraintLookup, V: VarNameLookup>(
        &self,
        elaborator: &mut Elaborator,
        _database: &C,
        var_lookup: &V,
    ) -> Result<(), ElaborationError> {
        elaborator.write_indented_var_list("right", &self.vars, var_lookup);
        Ok(())
    }
}

impl Elaboratable for OrderLeftVariablesRule {
    fn elaborate<C: ConstraintLookup, V: VarNameLookup>(
        &self,
        elaborator: &mut Elaborator,
        _database: &C,
        var_lookup: &V,
    ) -> Result<(), ElaborationError> {
        elaborator.write_indented_var_list("left", &self.vars, var_lookup);
        Ok(())
    }
}

impl Elaboratable for EqualsObjectiveRule {
    fn elaborate<C: ConstraintLookup, V: VarNameLookup>(
        &self,
        elaborator: &mut Elaborator,
        _database: &C,
        var_lookup: &V,
    ) -> Result<(), ElaborationError> {
        elaborator.writeln(&format!(
            "eobj {};",
            self.objective.to_pretty_string(var_lookup)
        ));
        Ok(())
    }
}

impl Elaboratable for DefineOrderRule {
    fn elaborate<C: ConstraintLookup, V: VarNameLookup>(
        &self,
        elaborator: &mut Elaborator,
        _database: &C,
        _var_lookup: &V,
    ) -> Result<(), ElaborationError> {
        elaborator.write_indent();
        elaborator.write(DEF_ORDER);
        elaborator.write(" ");
        elaborator.writeln(&self.name);
        elaborator.inc_indent();
        Ok(())
    }
}

impl Elaboratable for OrderSpecificationRule {
    fn elaborate<C: ConstraintLookup, V: VarNameLookup>(
        &self,
        elaborator: &mut Elaborator,
        _database: &C,
        _var_lookup: &V,
    ) -> Result<(), ElaborationError> {
        elaborator.write_indent();
        elaborator.writeln("spec");
        elaborator.inc_indent();

        Ok(())
    }
}

impl Elaboratable for MoveToCoreRule {
    fn elaborate<C: ConstraintLookup, V: VarNameLookup>(
        &self,
        elaborator: &mut Elaborator,
        database: &C,
        _var_lookup: &V,
    ) -> Result<(), ElaborationError> {
        elaborator.write("core");
        elaborator.write(" ");
        elaborator.write("id");
        for &index in self.constraint_ids.iter() {
            elaborator.write(" ");
            elaborator.write_constraint_out_id(database, index as usize);
        }
        elaborator.writeln(";");

        Ok(())
    }
}

impl Elaboratable for OrderTransitivityRule {
    fn elaborate<C: ConstraintLookup, V: VarNameLookup>(
        &self,
        elaborator: &mut Elaborator,
        _database: &C,
        _var_lookup: &V,
    ) -> Result<(), ElaborationError> {
        elaborator.write_indent();
        elaborator.writeln("transitivity");
        elaborator.inc_indent();
        Ok(())
    }
}

impl Elaboratable for OutputRule {
    fn elaborate<C: ConstraintLookup, V: VarNameLookup>(
        &self,
        elaborator: &mut Elaborator,
        _database: &C,
        _var_lookup: &V,
    ) -> Result<(), ElaborationError> {
        elaborator.write("output");
        elaborator.write(" ");
        match self.guarantee {
            OutputGuarantee::None => elaborator.write("NONE"),
            OutputGuarantee::Derivable => elaborator.write(DERIVABLE),
            OutputGuarantee::Equisatisfiable => elaborator.write(EQUISAT),
            OutputGuarantee::Equioptimal => elaborator.write(EQUIOPT),
            OutputGuarantee::Equienumerable => elaborator.write(EQUIENUM),
        }
        elaborator.write(" ");
        match self.output_type {
            OutputType::Implicit => elaborator.writeln("IMPLICIT;"),
            OutputType::File => elaborator.writeln("FILE;"),
            OutputType::Permutation => elaborator.writeln("PERMUTATION;"),
            OutputType::None => elaborator.writeln(";"),
        }
        Ok(())
    }
}

impl Elaboratable for AssertionRule {
    fn elaborate<C: ConstraintLookup, V: VarNameLookup>(
        &self,
        elaborator: &mut Elaborator,
        _database: &C,
        var_lookup: &V,
    ) -> Result<(), ElaborationError> {
        elaborator.write("a ");
        elaborator.write(&self.constraint.to_pretty_string(var_lookup));
        let has_annotations =
            self.id_list.is_some() || self.name.is_some() || self.free_text.is_some();
        if has_annotations {
            elaborator.write(" :");
            if let Some(id_list) = &self.id_list {
                for id in id_list {
                    elaborator.write(" ");
                    elaborator.write(&id.to_string());
                }
            }
            if self.name.is_some() || self.free_text.is_some() {
                elaborator.write(" :");
                if let Some(name) = &self.name {
                    elaborator.write(" ");
                    elaborator.write(name);
                }
                if let Some(free_text) = &self.free_text {
                    elaborator.write(" :");
                    elaborator.write(free_text);
                }
            }
        }
        elaborator.writeln(";");
        Ok(())
    }
}

impl Elaboratable for OrderReflexivityRule {
    fn elaborate<C: ConstraintLookup, V: VarNameLookup>(
        &self,
        elaborator: &mut Elaborator,
        _database: &C,
        _var_lookup: &V,
    ) -> Result<(), ElaborationError> {
        elaborator.write_indent();
        elaborator.writeln("reflexivity");
        elaborator.inc_indent();
        Ok(())
    }
}

impl Elaboratable for OrderFreshAux2Rule {
    fn elaborate<C: ConstraintLookup, V: VarNameLookup>(
        &self,
        elaborator: &mut Elaborator,
        _database: &C,
        var_lookup: &V,
    ) -> Result<(), ElaborationError> {
        elaborator.write_indented_var_list(FRESH_AUX_2, &self.vars, var_lookup);
        Ok(())
    }
}

impl Elaboratable for OrderDefConstraintRule {
    fn elaborate<C: ConstraintLookup, V: VarNameLookup>(
        &self,
        elaborator: &mut Elaborator,
        _database: &C,
        var_lookup: &V,
    ) -> Result<(), ElaborationError> {
        elaborator.write_indent();
        elaborator.write(&self.constraint.to_pretty_string(var_lookup));
        elaborator.writeln(";");
        Ok(())
    }
}

impl Elaboratable for PolRule {
    fn elaborate<C: ConstraintLookup, V: VarNameLookup>(
        &self,
        elaborator: &mut Elaborator,
        database: &C,
        var_lookup: &V,
    ) -> Result<(), ElaborationError> {
        elaborator.write_pol_step(&self.instructions, Some(database), Some(var_lookup));
        Ok(())
    }
}

impl Elaboratable for OrderProofRule {
    fn elaborate<C: ConstraintLookup, V: VarNameLookup>(
        &self,
        elaborator: &mut Elaborator,
        _database: &C,
        _var_lookup: &V,
    ) -> Result<(), ElaborationError> {
        elaborator.write_indent();
        elaborator.writeln("proof");
        elaborator.inc_indent();
        Ok(())
    }
}

impl Elaboratable for OrderVariablesRule {
    fn elaborate<C: ConstraintLookup, V: VarNameLookup>(
        &self,
        elaborator: &mut Elaborator,
        _database: &C,
        _var_lookup: &V,
    ) -> Result<(), ElaborationError> {
        elaborator.write_indent();
        elaborator.writeln("vars");
        elaborator.inc_indent();
        Ok(())
    }
}

impl Elaboratable for OrderFreshRightVariablesRule {
    fn elaborate<C: ConstraintLookup, V: VarNameLookup>(
        &self,
        elaborator: &mut Elaborator,
        _database: &C,
        var_lookup: &V,
    ) -> Result<(), ElaborationError> {
        elaborator.write_indented_var_list(FRESH_RIGHT, &self.vars, var_lookup);
        Ok(())
    }
}

impl Elaboratable for EqualsRule {
    fn elaborate<C: ConstraintLookup, V: VarNameLookup>(
        &self,
        elaborator: &mut Elaborator,
        database: &C,
        _var_lookup: &V,
    ) -> Result<(), ElaborationError> {
        if self.add_result {
            elaborator.write_indent();
            elaborator.write("pol ");
            elaborator.write_constraint_out_id(database, self.hint.unwrap() as usize);
            elaborator.writeln(";");
        }

        Ok(())
    }
}

impl Elaboratable for OrderFreshAux1Rule {
    fn elaborate<C: ConstraintLookup, V: VarNameLookup>(
        &self,
        elaborator: &mut Elaborator,
        _database: &C,
        var_lookup: &V,
    ) -> Result<(), ElaborationError> {
        elaborator.write_indented_var_list(FRESH_AUX_1, &self.vars, var_lookup);
        Ok(())
    }
}

impl Elaboratable for StrengtheningToCoreRule {
    fn elaborate<C: ConstraintLookup, V: VarNameLookup>(
        &self,
        elaborator: &mut Elaborator,
        _database: &C,
        _var_lookup: &V,
    ) -> Result<(), ElaborationError> {
        elaborator.writeln(&format!(
            "{STRENGTHENING_TO_CORE} {};",
            if self.enable { "on" } else { "off" }
        ));
        Ok(())
    }
}

impl Elaboratable for EndProof {
    fn elaborate<C: ConstraintLookup, V: VarNameLookup>(
        &self,
        elaborator: &mut Elaborator,
        _database: &C,
        _var_lookup: &V,
    ) -> Result<(), ElaborationError> {
        elaborator.writeln(PROOF_END);
        Ok(())
    }
}

impl Elaboratable for ScopeRule {
    fn elaborate<C: ConstraintLookup, V: VarNameLookup>(
        &self,
        elaborator: &mut Elaborator,
        _database: &C,
        _var_lookup: &V,
    ) -> Result<(), ElaborationError> {
        elaborator.write_indent();
        elaborator.write("scope ");
        elaborator.writeln(&self.id.to_string());
        elaborator.inc_indent();
        Ok(())
    }
}

impl Elaboratable for ObjectiveValueRule {
    fn elaborate<C: ConstraintLookup, V: VarNameLookup>(
        &self,
        elaborator: &mut Elaborator,
        _database: &C,
        _var_lookup: &V,
    ) -> Result<(), ElaborationError> {
        elaborator.write_objective_value(&self.value);
        Ok(())
    }
}

// Rules that write nothing here.
// Some are no-ops, and some have their elaboration dealt with
// via `write_*` helpers during checking.
impl Elaboratable for Comment {}
impl Elaboratable for DominanceBasedStrengtheningRule {}
impl Elaboratable for EndTimerRule {}
impl Elaboratable for FailRule {}
impl Elaboratable for FormulaCheck {}
impl Elaboratable for HeaderRule {}
impl Elaboratable for IsDeletedCheck {}
impl Elaboratable for ObjectiveUpdateRule {}
impl Elaboratable for PreservedAddRule {}
impl Elaboratable for PreservedRemoveRule {}
impl Elaboratable for ProofByContradiction {}
impl Elaboratable for RedundanceBasedStrengtheningRule {}
impl Elaboratable for RUPRule {}
impl Elaboratable for SetLevelRule {}
impl Elaboratable for StartTimerRule {}
impl Elaboratable for UnimplementedRule {}
