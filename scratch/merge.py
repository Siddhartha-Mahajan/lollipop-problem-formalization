import re,os
R='/Users/siddhartha/Lossfunk/lollipop_end_to_end_formalization/'
imp=lambda f:open(R+'scratch/impl/'+f+'.lean').read()
OLD="""import old_lean_folder.Concrete.EndToEnd.PrimitiveArcs
import old_lean_folder.Concrete.EndToEnd.CircleJordan
import old_lean_folder.Concrete.EndToEnd.SimpleArcComplement
import old_lean_folder.Concrete.EndToEnd.JordanBridge
import old_lean_folder.Concrete.EndToEnd.Compactification
import old_lean_folder.Concrete.EndToEnd.ArcClosedCurve
import Mathlib.Tactic
"""
OPEN="""
noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd
namespace Pieces

open Set

"""
CLOSE="""
end Pieces
end EndToEnd
end Concrete
end Lollipop
"""
def write(name,imports,body):
    open(R+'Carrier/'+name+'.lean','w').write(imports+OPEN+body+CLOSE)
def body_of(src):
    # between 'open Set' and final 'end Pieces'
    i=src.index('open Set\n')+len('open Set\n')
    j=src.rindex('end Pieces')
    return src[i:j]
# Defs
spec=open(R+'scratch/Spec.lean').read()
a=spec.index('/-- Rotation of a plane vector')
b=spec.index('/-! ### Task A1')
c=spec.index('/-- Simple arc in the one-point compactification')
d=spec.index('/-! ### Task B2')
write('Defs',OLD,spec[a:b]+spec[c:d])
# CircleCollars
s=imp('CircleCollars')
body=body_of(s)
k=body.index('/-! ### Helper lemmas -/')
body=body[k:].replace('section Helpers','namespace CircleAux',1).replace('end Helpers','end CircleAux\nopen CircleAux',1)
write('CircleCollars','import Carrier.Defs\nimport Mathlib.Analysis.SpecialFunctions.PolarCoord\n',body)
# StemCollars
s=imp('StemCollars'); body=body_of(s)
k=body.index('/-- The strip map')
body='namespace StemAux\n\n'+body[k:]+'\nend StemAux\nexport StemAux (seg_collars ray_collars seg_leaf_collar ray_leaf_collar)\n'
write('StemCollars','import Carrier.Defs\n',body)
# LocalSides
s=imp('LocalSides'); write('LocalSides','import Carrier.Defs\n',body_of(s))
# SphereArcs
s=imp('SphereArcs'); body=body_of(s)
k=body.index('theorem IsSphereArc.trans')
# keep preceding comment lines? find '/-' before
k2=body.rfind('/-!',0,k)
write('SphereArcs','import Carrier.Defs\n',body[k2 if k2>=0 else k:])
# SphereSides
s=imp('SphereSides'); body=body_of(s)
k=body.index('/-- Statement of Task B1')
body=body[k:].replace('theorem sphere_local_sides_separated (hB1','theorem sphere_local_sides_separated_of (hB1',1)
body+="""
theorem sphere_local_sides_separated
    (q : Point) {R G : Set Sphere2} {u v : Sphere2} (huv : u ≠ v)
    (hR : IsSphereArc R u v) (hG : IsSphereArc G u v) (hRG : R ∩ G = {u, v})
    (hqR : finitePoint q ∉ R) (hqG : finitePoint q ∉ G)
    {N N₁ N₂ : Set Point} (hN : IsOpen N) (hqN : q ∉ N)
    (hNJ : finiteLift N ∩ (R ∪ G) = G \\ {u, v})
    (hN₁ : IsPreconnected N₁) (hN₂ : IsPreconnected N₂)
    (hne₁ : N₁.Nonempty) (hne₂ : N₂.Nonempty)
    (hN₁N : N₁ ⊆ N) (hN₂N : N₂ ⊆ N)
    (hN₁J : ∀ p ∈ N₁, finitePoint p ∉ R ∪ G)
    (hN₂J : ∀ p ∈ N₂, finitePoint p ∉ R ∪ G)
    (hcov : ∀ p ∈ N, finitePoint p ∉ R ∪ G → p ∈ N₁ ∨ p ∈ N₂) :
    ∀ W : Set Point, IsPreconnected W → q ∉ W →
      (∀ p ∈ W, finitePoint p ∉ R ∪ G) →
      ∀ n₁ ∈ N₁, ∀ n₂ ∈ N₂, ¬ (n₁ ∈ W ∧ n₂ ∈ W) :=
  sphere_local_sides_separated_of
    (fun {J R γ N N₁ N₂ u v} => local_sides_separated (J := J) (R := R) (γ := γ) (N := N) (N₁ := N₁) (N₂ := N₂) (u := u) (v := v))
    q huv hR hG hRG hqR hqG hN hqN hNJ hN₁ hN₂ hne₁ hne₂ hN₁N hN₂N hN₁J hN₂J hcov
"""
write('SphereSides','import Carrier.LocalSides\nimport Mathlib.Geometry.Euclidean.Inversion.Calculus\n',body)
# HatArcs
s=imp('HatArcs'); body=body_of(s)
k=body.index('/-! ### Lifting planar arcs -/')
body=body[k:]
k2=body.index('/-! ### Stem rays -/')
body=body[:k2]+'namespace HatAux\n\n'+body[k2:]+'\nend HatAux\nexport HatAux (raySet_isSphereArc hatCarrier_arc_to_infinity)\n'
write('HatArcs','import Carrier.SphereArcs\n',body)
