import Hypergraph.HyperImplC
import Hypergraph.SiteOneArm
import Hypergraph.SiteEndgame

/-!
# Renormalization certificates

The below-parameter route to `SiteCriticality` runs as follows.  From percolation at a parameter `p`
one extracts a *certificate*: a finite list of events, each depending on finitely many sites, each
holding at `p` with strict slack.  Because there are finitely many of them and each is a cylinder
event, their probabilities are Lipschitz in the parameter, so the whole list still holds at every
parameter close enough to `p`, in particular at some `q < p`.  A certificate that holds at `q` is
built so as to force percolation in a slab at `q`.  Then `siteCriticality_of_slabReductionBelow'`
finishes, with no theorem about percolation at a critical point anywhere in the argument.

This module fixes the data and the two propositions that the geometric work has to supply.
-/

noncomputable section

namespace KNAll.Site

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels

variable {d : ℕ}

/-- An event depending on finitely many sites, together with that finite set. -/
structure CylinderExperiment (d : ℕ) where
  /-- The sites the event depends on. -/
  support : Finset (Site d)
  /-- The event. -/
  event : Set (SiteConfig (Site d))
  /-- It depends only on the sites of `support`. -/
  determined : DeterminedBy event (↑support : Set (Site d))
  /-- It is measurable. -/
  measurable' : MeasurableSet event

/-- The probability of a cylinder event at the constant parameter `q`. -/
def CylinderExperiment.prob (E : CylinderExperiment d) (q : unitInterval) : ℝ :=
  (siteBernoulli (fun _ : Site d => q)).real E.event

/-- The finite data extracted from percolation at one parameter: a slab width, a density for the
comparison lattice, and finitely many cylinder events with thresholds. -/
structure RenormData (d : ℕ) where
  /-- The width of the slab the certificate produces percolation in. -/
  slabWidth : ℕ
  /-- The density of the comparison site percolation on the plane. -/
  macroDensity : ℝ
  /-- How many probability bounds the certificate carries. -/
  numBounds : ℕ
  /-- The events. -/
  bound : Fin numBounds → CylinderExperiment d
  /-- The thresholds they must exceed. -/
  threshold : Fin numBounds → ℝ

/-- A certificate holds at `q` when every one of its finitely many bounds holds strictly. -/
def RenormData.ValidAt (C : RenormData d) (q : unitInterval) : Prop :=
  ∀ i, C.threshold i < (C.bound i).prob q

/-- **The geometric input, first half.**  Percolation at a parameter strictly inside the unit
interval yields a certificate valid there. -/
def CertificateExtraction (d : ℕ) [NeZero d] : Prop :=
  ∀ p : unitInterval, 0 < (p : ℝ) → (p : ℝ) < 1 → 0 < thetaSite d p →
    ∃ C : RenormData d, C.ValidAt p

/-- **The geometric input, second half.**  A valid certificate forces percolation in its slab. -/
def CertificateSoundness (d : ℕ) [NeZero d] : Prop :=
  ∀ (C : RenormData d) (q : unitInterval), C.ValidAt q →
    0 < thetaSiteOn (slabGraph d C.slabWidth) (slabOrigin d C.slabWidth) q

end KNAll.Site

end
