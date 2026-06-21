import Lollipop.Internal.Manuscript.CompleteFormalization.OEISGeometry
import Lollipop.Internal.Manuscript.CompleteFormalization.OEISPair02
import Lollipop.Internal.Manuscript.CompleteFormalization.OEISPair03
import Lollipop.Internal.Manuscript.CompleteFormalization.OEISPair12
import Lollipop.Internal.Manuscript.CompleteFormalization.OEISPair13
import Lollipop.Internal.Manuscript.CompleteFormalization.OEISPair23

/-!
Concrete OEIS/Karlsson base-coordinate certificates.

This file is deliberately only an assembler.  The actual coordinate witnesses
and their membership/cardinality proofs live in the `OEISGeometry` and
`OEISPair*` files.
-/

namespace Lollipop
namespace TheoremOneManuscript
namespace CompleteFormalization

noncomputable section

/-- Bundled six-pair coordinate crossing certificate for the exact
OEIS/Karlsson four-base arrangement. -/
noncomputable def karlsson_oeis_base_six_pair_coordinate_crossing_certificate :
    ExplicitInputs.KarlssonOEISBaseSixPairCoordinateCrossingCertificate where
  pair01 := OEISGeometry.q0q1PairCoordinateCrossingCertificate
  pair02 := OEISPair02.q0q2PairCoordinateCrossingCertificate
  pair03 := OEISPair03.q0q3PairCoordinateCrossingCertificate
  pair12 := OEISPair12.q1q2PairCoordinateCrossingCertificate
  pair13 := OEISPair13.q1q3PairCoordinateCrossingCertificate
  pair23 := OEISPair23.q2q3PairCoordinateCrossingCertificate

/-- All-at-once coordinate crossing certificate for the exact OEIS/Karlsson
four-base arrangement, assembled from the six proved local pair certificates. -/
noncomputable def karlsson_oeis_base_coordinate_crossing_certificate :
    ExplicitInputs.KarlssonOEISBaseCoordinateCrossingCertificate :=
  karlsson_oeis_base_six_pair_coordinate_crossing_certificate
    |>.toCoordinateCrossingCertificate

end

end CompleteFormalization
end TheoremOneManuscript
end Lollipop
