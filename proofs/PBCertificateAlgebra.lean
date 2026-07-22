/-!
Bootstrap obligations for the AY CertCut PB-COMP program.

This file records a small Prop-level Track A certificate-algebra contract
as explicit proof obligations: ay may only promote a PB operation when the
operation has evidence, checker replay, and the corresponding soundness arrow.
The arithmetic normalization kernel remains a separate refinement target.
-/

def ay_certcut_conj (p q : Prop) : Prop := p ∧ q

def ay_certcut_disj (p q : Prop) : Prop := p ∨ q

def ay_certcut_pb_constraint
    (normalForm integerCoefficients booleanLiterals lowerBound : Prop) :
    Prop :=
  ay_certcut_conj normalForm
    (ay_certcut_conj integerCoefficients
      (ay_certcut_conj booleanLiterals lowerBound))

def ay_certcut_certificate_step
    (premises conclusion checkerReplay : Prop) : Prop :=
  ay_certcut_conj premises (ay_certcut_conj conclusion checkerReplay)

def ay_certcut_pb_add_sound
    (leftHolds rightHolds sumHolds : Prop) : Prop :=
  leftHolds -> rightHolds -> sumHolds

def ay_certcut_rhs_weaken_sound
    (rhsOrder strongerHolds weakerHolds : Prop) : Prop :=
  rhsOrder -> strongerHolds -> weakerHolds

def ay_certcut_scaling_sound
    (positiveScale inputHolds scaledHolds : Prop) : Prop :=
  positiveScale -> inputHolds -> scaledHolds

def ay_certcut_rounding_sound
    (divisionSideCondition inputHolds roundedHolds : Prop) : Prop :=
  divisionSideCondition -> inputHolds -> roundedHolds

def ay_certcut_saturation_sound
    (saturationSideCondition inputHolds saturatedHolds : Prop) : Prop :=
  saturationSideCondition -> inputHolds -> saturatedHolds

def ay_certcut_residue_pair_lift_sound
    (residueOne checkerReplay lowerBoundLift : Prop) : Prop :=
  residueOne -> checkerReplay -> lowerBoundLift

def ay_certcut_zero_bound_refutation_sound
    (lowerBoundLift zeroUpperBound contradiction : Prop) : Prop :=
  lowerBoundLift -> zeroUpperBound -> contradiction

def ay_certcut_track_a_gate
    (addition weakening scaling rounding saturation veripbReplay : Prop) :
    Prop :=
  ay_certcut_conj addition
    (ay_certcut_conj weakening
      (ay_certcut_conj scaling
        (ay_certcut_conj rounding
          (ay_certcut_conj saturation veripbReplay))))

def ay_certcut_track_b_gate
    (residueDetection residueLift liftedCutReplay benchmarkEvidence : Prop) :
    Prop :=
  ay_certcut_conj residueDetection
    (ay_certcut_conj residueLift
      (ay_certcut_conj liftedCutReplay benchmarkEvidence))

def ay_certcut_no_public_claim (diagnostic : Prop) : Prop := diagnostic

theorem ay_certcut_pb_add_obligation
    {leftHolds rightHolds sumHolds : Prop} :
    ay_certcut_pb_add_sound leftHolds rightHolds sumHolds ->
    leftHolds -> rightHolds -> sumHolds :=
  fun sound leftEvidence rightEvidence => sound leftEvidence rightEvidence

theorem ay_certcut_rhs_weaken_obligation
    {rhsOrder strongerHolds weakerHolds : Prop} :
    ay_certcut_rhs_weaken_sound rhsOrder strongerHolds weakerHolds ->
    rhsOrder -> strongerHolds -> weakerHolds := by
  intro sound
  intro order
  intro stronger
  exact sound order stronger

theorem ay_certcut_scaling_obligation
    {positiveScale inputHolds scaledHolds : Prop} :
    ay_certcut_scaling_sound positiveScale inputHolds scaledHolds ->
    positiveScale -> inputHolds -> scaledHolds := by
  intro sound
  intro scale
  intro input
  exact sound scale input

theorem ay_certcut_rounding_obligation
    {divisionSideCondition inputHolds roundedHolds : Prop} :
    ay_certcut_rounding_sound divisionSideCondition inputHolds roundedHolds ->
    divisionSideCondition -> inputHolds -> roundedHolds := by
  intro sound
  intro sideCondition
  intro input
  exact sound sideCondition input

theorem ay_certcut_saturation_obligation
    {saturationSideCondition inputHolds saturatedHolds : Prop} :
    ay_certcut_saturation_sound saturationSideCondition inputHolds
      saturatedHolds ->
    saturationSideCondition -> inputHolds -> saturatedHolds := by
  intro sound
  intro sideCondition
  intro input
  exact sound sideCondition input

theorem ay_certcut_residue_pair_lift_obligation
    {residueOne checkerReplay lowerBoundLift : Prop} :
    ay_certcut_residue_pair_lift_sound residueOne checkerReplay
      lowerBoundLift ->
    residueOne -> checkerReplay -> lowerBoundLift := by
  intro sound
  intro residue
  intro replay
  exact sound residue replay

theorem ay_certcut_zero_bound_refutation_obligation
    {lowerBoundLift zeroUpperBound contradiction : Prop} :
    ay_certcut_zero_bound_refutation_sound lowerBoundLift zeroUpperBound
      contradiction ->
    lowerBoundLift -> zeroUpperBound -> contradiction :=
  fun sound liftEvidence upperEvidence => sound liftEvidence upperEvidence

theorem ay_certcut_track_a_acceptance
    {addition weakening scaling rounding saturation veripbReplay : Prop} :
    ay_certcut_track_a_gate addition weakening scaling rounding saturation
      veripbReplay ->
    ay_certcut_track_a_gate addition weakening scaling rounding saturation
      veripbReplay :=
  fun gate => gate

theorem ay_certcut_track_b_acceptance
    {residueDetection residueLift liftedCutReplay benchmarkEvidence : Prop} :
    ay_certcut_track_b_gate residueDetection residueLift liftedCutReplay
      benchmarkEvidence ->
    ay_certcut_track_b_gate residueDetection residueLift liftedCutReplay
      benchmarkEvidence :=
  fun gate => gate

theorem ay_certcut_fail_closed_claim_policy
    {diagnostic : Prop} :
    diagnostic -> ay_certcut_no_public_claim diagnostic := by
  intro evidence
  exact evidence
