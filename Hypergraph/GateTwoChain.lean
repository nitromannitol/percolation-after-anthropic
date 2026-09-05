import Hypergraph.SiteLocalFromUniqueness
import Hypergraph.SiteIntrinsicInputs

/-!
# The local inputs, from supercriticality alone

Site Burton-Keane uniqueness, the ambient local inputs derived from it, and the transfer of those
to events determined by a finite box were proved by three agents working separately.  This file
composes them: supercriticality alone now yields the finite-box cylinder events that the
renormalisation certificate consumes.
-/

namespace KNAll.Site

/-- From `theta > 0`, the confined finite-box local inputs. -/
theorem siteIntrinsicInputs_of_thetaSite_pos (d : ℕ) (p : unitInterval)
    (hp : 0 < thetaSite d p) : SiteIntrinsicInputs d p :=
  siteIntrinsicInputs_of_siteLocalInputs d p (siteLocalInputs_of_thetaSite_pos d p hp)

end KNAll.Site
