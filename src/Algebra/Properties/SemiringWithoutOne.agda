------------------------------------------------------------------------
-- The Agda standard library
--
-- Some basic properties of Semirings without a multiplicative identity
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Bundles using (SemiringWithoutOne)

module Algebra.Properties.SemiringWithoutOne {c ℓ} (semiring : SemiringWithoutOne c ℓ) where

open SemiringWithoutOne semiring

import Algebra.Consequences.Setoid setoid as Consequences
open import Algebra.Properties.CommutativeMonoid (+-commutativeMonoid) public
  using ()
  renaming
    ( x∙yz≈xy∙z to x+[y+z]≈[x+y]+z
    ; alternativeˡ to +-alternativeˡ
    ; alternativeʳ to +-alternativeʳ
    ; alternative to +-alternative
    ; flexible to +-flexible

    ; uv≈w⇒xu∙v≈xw to u+v≈w⇒[x+u]+v≈x+w
    ; uv≈w⇒u∙vx≈wx to u+v≈w⇒u+[v+x]≈w+x
    ; uv≈w⇒u[vx∙y]≈w∙xy to u+v≈w⇒u+[[v+x]+y]≈w+[x+y]
    ; uv≈w⇒[x∙yu]v≈x∙yw to u+v≈w⇒[x+[y+u]]+v≈x+[y+w]
    ; uv≈w⇒[xu∙v]y≈x∙wy to u+v≈w⇒[[x+u]+v]+y≈x+[w+y]
    ; uv≈w⇒[xy∙u]v≈x∙yw to u+v≈w⇒[[x+y]+u]+v≈x+[y+w]

    ; uv≈w⇒xu∙vy≈x∙wy to u+v≈w⇒[x+u]+[v+y]≈x+[w+y]
    ; uv≈w⇒xy≈z⇒u[vx∙y]≈wz to u+v≈w⇒x+y≈z⇒u+[[v+x]+y]≈w+z
    ; uv≈w⇒x∙wy≈x∙[u∙vy] to u+v≈w⇒x+[w+y]≈x+[u+[v+y]]

    ; [uv∙w]x≈u[vw∙x] to [[u+v]+w]+x≈u+[[v+w]+x]
    ; [uv∙w]x≈u[v∙wx] to [[u+v]+w]+x≈u+[v+[w+z]]
    ; [u∙vw]x≈uv∙wx to [u+[v+w]]+x≈[u+v]+[w+x]
    ; [u∙vw]x≈u[v∙wx] to [u+[v+w]]+x≈u+[v+[w+x]]
    ; uv∙wx≈u[vw∙x] to [u+v]+[w+x]≈u+[[v+w]+x]

    ; uv≈wx⇒yu∙v≈yw∙x to u+v≈w+x⇒[y+u]+v≈[y+w]+x
    ; uv≈wx⇒u∙vy≈w∙xy to u+v≈w+x⇒u+[v+y]≈w+[x+y]
    ; uv≈wx⇒yu∙vz≈yw∙xz to u+v≈w+x⇒[y+u]+[v+z]≈[y+w]+[x+z]

    ; medial to +-medial

    ; x∙yz≈y∙xz to x+[y+z]≈y+[x+z]
    ; x∙yz≈z∙yx to x+[y+z]≈z+[y+x]
    ; x∙yz≈x∙zy to x+[y+z]≈x+[z+y]
    ; x∙yz≈y∙zx to x+[y+z]≈y+[z+x]
    ; x∙yz≈z∙xy to x+[y+z]≈z+[x+y]

    ; x∙yz≈yx∙z to x+[y+z]≈[y+x]+z
    ; x∙yz≈zy∙x to x+[y+z]≈[z+y]+x
    ; x∙yz≈xz∙y to x+[y+z]≈[x+z]+y
    ; x∙yz≈yz∙x to x+[y+z]≈[y+z]+x
    ; x∙yz≈zx∙y to x+[y+z]≈[z+x]+y

    ; xy∙z≈y∙xz to [x+y]+z≈y+[x+z]
    ; xy∙z≈z∙yx to [x+y]+z≈z+[y+x]
    ; xy∙z≈x∙zy to [x+y]+z≈x+[z+y]
    ; xy∙z≈y∙zx to [x+y]+z≈y+[z+x]
    ; xy∙z≈z∙xy to [x+y]+z≈z∙[x+y]

    ; xy∙z≈yx∙z to [x+y]+z≈[y+x]+z
    ; xy∙z≈zy∙x to [x+y]+z≈[z+y]+x
    ; xy∙z≈xz∙y to [x+y]+z≈[x+z]+y
    ; xy∙z≈yz∙x to [x+y]+z≈[y+z]+x
    ; xy∙z≈zx∙y to [x+y]+z≈[z+x]+y

    ; xy∙xx≈x∙yxx to [x+y]+[x+x]≈x+[y+x+x]

    ; semimedialˡ to +-semimedialˡ
    ; semimedialʳ to +-semimedialʳ
    ; middleSemimedial to +-middleSemimedial
    ; semimedial to +-semimedial

    ; ε-unique to 0#-unique
    
    ; elimʳ to +-elimʳ
    ; elimˡ to +-elimˡ
    ; introʳ to +-introʳ
    ; introˡ to +-introˡ
    ; introᶜ to +-introᶜ

    ; cancelʳ to +-cancelʳ
    ; cancelˡ to +-cancelˡ
    ; insertˡ to +-insertˡ
    ; insertʳ to +-insertʳ
    ; cancelᶜ to +-cancelᶜ
    ; insertᶜ to +-insertᶜ
    )

open import Algebra.Properties.Semigroup (*-semigroup)
  using ()
  renaming
    ( x∙yz≈xy∙z to x*yz≈xy*z
    ; alternativeˡ to *-alternativeˡ
    ; alternativeʳ to *-alternativeʳ
    ; alternative to *-alternative
    ; flexible to *-flexible

    ; uv≈w⇒xu∙v≈xw to uv≈w⇒xu*v≈xw
    ; uv≈w⇒u∙vx≈wx to uv≈w⇒u*vx≈wx
    ; uv≈w⇒u[vx∙y]≈w∙xy to uv≈w⇒u[vx*y]≈w*xy
    ; uv≈w⇒[x∙yu]v≈x∙yw to uv≈w⇒[x*yu]v≈x*yw
    ; uv≈w⇒[xu∙v]y≈x∙wy to uv≈w⇒[xu*v]y≈x*wy
    ; uv≈w⇒[xy∙u]v≈x∙yw to uv≈w⇒[xy*u]v≈x*yw

    ; uv≈w⇒xu∙vy≈x∙wy to uv≈w⇒xu*vy≈x*wy
    ; uv≈w⇒xy≈z⇒u[vx∙y]≈wz to uv≈w⇒xy≈z⇒u[vx*y]≈wz
    ; uv≈w⇒x∙wy≈x∙[u∙vy] to uv≈w⇒x*wy≈x[u*vy]

    ; [uv∙w]x≈u[vw∙x] to [uv*w]x≈u[vw*x]
    ; [uv∙w]x≈u[v∙wx] to [uv*w]x≈u[v*wz]
    ; [u∙vw]x≈uv∙wx to [u*vw]x≈uv*wx
    ; [u∙vw]x≈u[v∙wx] to [u*vw]x≈u[v*wx]
    ; uv∙wx≈u[vw∙x] to uv*wx≈u[vw*x]

    ; uv≈wx⇒yu∙v≈yw∙x to uv≈wx⇒yu*v≈yw*x
    ; uv≈wx⇒u∙vy≈w∙xy to uv≈wx⇒u*vy≈w*xy
    ; uv≈wx⇒yu∙vz≈yw∙xz to uv≈wx⇒yu*vz≈yw*xz
    )

binomial-expansion : ∀ w x y z →
                     (w + x) * (y + z) ≈ w * y + w * z + x * y + x * z
binomial-expansion = Consequences.binomial-expansion +-cong +-assoc distrib
