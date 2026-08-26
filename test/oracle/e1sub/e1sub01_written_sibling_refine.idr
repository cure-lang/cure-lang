%default total

-- E1-sub mirror: matching the evidence `RIsA` refines the sibling `r` to `RA`, and
-- that refinement must reach the WRITTEN body term `project k r` so it becomes
-- convertible with the goal RHS `project k RA`. Idris refines `r := RA` on the
-- `RIsA` match and `Refl` closes `project k r = project k RA`; Cure now reaches the
-- written occurrence of `r` the same way.
--
-- `r` is IMPLICIT here (solved by the `RoleIs` index the evidence carries); Cure
-- spells it explicit. Idris rejects a bare explicit pattern variable in a forced
-- position (it must be dotted/implicit), so the implicit form is the faithful
-- idiom — the same proof, each language's spelling (cf. the e8seq mirror, where a
-- measure index is implicit in Idris and explicit in Cure).

data Role = RA | RB
data TB2 = T | F

role_eq : Role -> Role -> TB2
role_eq RA RA = T
role_eq RA RB = F
role_eq RB RA = F
role_eq RB RB = T

data Tag = TA | TB
data Local = LEnd | LSend Tag Local
data Global = GEnd | GMsg Role Tag Global

project : Global -> Role -> Local
project GEnd            r = LEnd
project (GMsg from t k) r = case role_eq from r of
  T => LSend t (project k r)
  F => project k r

data RoleIs : Role -> Type where
  RIsA : RoleIs RA

use_it : {r : Role} -> (k : Global) -> RoleIs r -> project k r = project k RA
use_it k RIsA = Refl
