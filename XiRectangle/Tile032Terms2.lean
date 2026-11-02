/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
module

public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile032Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨32,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((7/8), (8037/640)), 0, by norm_num⟩
  | 1 => ⟨(1, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_variable : Sound J_variable F_variable c := by
  have h := variable_sound 12 ((7/8), (8037/640))
  have he : value ((7/8), (8037/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_log16 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2772588722239781/1000000000000000), 0), (3/500000000000000), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_log16 : Sound J_log16 F_log16 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log16_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog16 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-372130559/134217728), 0), (1/536870912), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_negLog16 : Sound J_negLog16 F_negLog16 c := by
  apply sound_round (sound_scale (A_log16 hcre) S_log16)
  intro k
  fin_cases k <;> norm_num [J_negLog16, J_log16, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg16 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-10175445/4194304), (-584143223/16777216)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-372130559/134217728), 0), (1/536870912), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_arg16 : Sound J_arg16 F_arg16 c := by
  apply sound_round (sound_mul (A_negLog16 hcre) (A_variable hcre) S_negLog16 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg16, J_negLog16, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term16 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1538693641947651/18014398509481984), (409540038194555/18014398509481984)), (276999709/18014398509481984), by norm_num⟩
  | 1 => ⟨((1017132911/4294967296), (-67680245/1073741824)), (185/4294967296), by norm_num⟩
  | 2 => ⟨((-1410045619/4294967296), (46912371/536870912)), (129/2147483648), by norm_num⟩
  | 3 => ⟨((325789715/1073741824), (-346849895/4294967296)), (241/4294967296), by norm_num⟩
  | 4 => ⟨((-451640445/2147483648), (240418027/4294967296)), (169/4294967296), by norm_num⟩
  | 5 => ⟨((250442641/2147483648), (-66658031/2147483648)), (189/8589934592), by norm_num⟩
  | 6 => ⟨((-925832589/17179869184), (246420407/17179869184)), (177/17179869184), by norm_num⟩
  | 7 => ⟨((1466830283/68719476736), (-48801603/8589934592)), (283/68719476736), by norm_num⟩
  | 8 => ⟨((-1016729275/137438953472), (67653387/34359738368)), (99/68719476736), by norm_num⟩
  | 9 => ⟨((626438249/274877906944), (-166733349/274877906944)), (123/274877906944), by norm_num⟩
  | 10 => ⟨((-347371125/549755813888), (184913201/1099511627776)), (275/2199023255552), by norm_num⟩
  | 11 => ⟨((700448919/4398046511104), (-186432093/4398046511104)), (279/8796093022208), by norm_num⟩
  | 12 => ⟨((-323676129/8796093022208), (344599679/35184372088832)), (65/8796093022208), by norm_num⟩
  | _ => zero

def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395203902880331/2535301200456458802993406410752), (3753426672983/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889108489131897/316912650057057350374175801344), (554926158995/79228162514264337593543950336)), (92637/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472280167391711/9903520314283042199192993792), (4993257357009/39614081257132168796771975168)), (104245/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944428181498979/1237940039285380274899124224), (5304020235915/2475880078570760549798248448)), (110793/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((110657624224029/9671406556917033397649408), (1325635062659/38685626227668133590597632)), (55415/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548925855901375/9671406556917033397649408), (4969559313849/9671406556917033397649408)), (51971/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314559724392485/151115727451828646838272), (4346792580193/604462909807314587353088)), (90989/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((235862175166195/9444732965739290427392), (3530295764515/37778931862957161709568)), (18491/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1296867385428629/4722366482869645213696), (5292866282657/4722366482869645213696)), (111011/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405130565002551/147573952589676412928), (3636752162511/295147905179352825856)), (152743/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822314661903029/73786976294838206464), (4542801321243/36893488147419103232)), (191085/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910674154276447/4611686018427387904), (10212675042093/9223372036854775808)), (215185/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592592277646601/1152921504606846976), (10201896124747/1152921504606846976)), (107727/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193356288607265/144115188075855872), (2228635269649/36028797018963968)), (23603/18014398509481984), by norm_num⟩
  | 4 => ⟨((1489790550250715/36028797018963968), (13347596206053/36028797018963968)), (141921/18014398509481984), by norm_num⟩
  | 3 => ⟨((1486931457716989/9007199254740992), (8321082402085/4503599627370496)), (355863/9007199254740992), by norm_num⟩
  | 2 => ⟨((1111621500588879/2251799813685248), (16578762299001/2251799813685248)), (357457/2251799813685248), by norm_num⟩
  | 1 => ⟨((552228931267619/562949953421312), (12354981962107/562949953421312)), (270091/562949953421312), by norm_num⟩
  | 0 => ⟨((1082921276688667/1125899906842624), (24394587573223/562949953421312)), (1096417/1125899906842624), by norm_num⟩
  | _ => zero

def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((1082921276688667/1125899906842624), (24394587573223/562949953421312)), (4182498936179732921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1039469051183721/1125899906842624), (46926760999867/562949953421312)), (275519/140737488355328), by norm_num⟩
  | 2 => ⟨((59490602709435/70368744177664), (346595042313829/2251799813685248)), (4437367/1125899906842624), by norm_num⟩
  | 3 => ⟨((1556063211986147/2251799813685248), (146507858029223/562949953421312)), (8868801/1125899906842624), by norm_num⟩
  | 4 => ⟨((922772915975609/2251799813685248), (809931635168095/2251799813685248)), (33746893/2251799813685248), by norm_num⟩
  | 5 => ⟨((86828589124039/2251799813685248), (663809431178347/2251799813685248)), (103869617/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1538693641947651/18014398509481984), (409540038194555/18014398509481984)), (276999709/18014398509481984), by norm_num⟩
  | _ => zero

def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-10175445/4194304), (-584143223/16777216)), (1/16777216), by norm_num⟩, -6, term16ValuePoly, term16ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term16Value_checks : CertifiedScalarExp.Checks term16Value := by
  constructor
  · norm_num [term16Value, CertifiedScalarExp.reduced, term16ValuePoly, term16ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term16Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term16ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term16Value, term16ValueSquares, term16ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term16Value, CertifiedScalarExp.roundingCheck, term16ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term16 : Sound J_term16 F_term16 c := by
  apply exp_sound (A_arg16 hcre) S_arg16 term16Value term16Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term16Value,J_arg16]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term16,J_arg16,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log17 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((354151668007027/125000000000000), 0), (3/500000000000000), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_log17 : Sound J_log17 F_log17 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log17_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog17 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-190133729/67108864), 0), (1/536870912), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_negLog17 : Sound J_negLog17 F_negLog17 c := by
  apply sound_round (sound_scale (A_log17 hcre) S_log17)
  intro k
  fin_cases k <;> norm_num [J_negLog17, J_log17, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg17 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-41591753/16777216), (-1193831859/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-190133729/67108864), 0), (1/536870912), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_arg17 : Sound J_arg17 F_arg17 c := by
  apply sound_round (sound_mul (A_negLog17 hcre) (A_variable hcre) S_negLog17 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg17, J_negLog17, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term17 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-788425436193543/18014398509481984), (643911003190975/9007199254740992)), (272757439/18014398509481984), by norm_num⟩
  | 1 => ⟨((266287025/2147483648), (-217477947/1073741824)), (93/2147483648), by norm_num⟩
  | 2 => ⟨((-754447953/4294967296), (1232322843/4294967296)), (133/2147483648), by norm_num⟩
  | 3 => ⟨((712504003/4294967296), (-581905587/2147483648)), (127/2147483648), by norm_num⟩
  | 4 => ⟨((-252334481/2147483648), (824331337/4294967296)), (91/2147483648), by norm_num⟩
  | 5 => ⟨((571933935/8589934592), (-467101309/4294967296)), (13/536870912), by norm_num⟩
  | 6 => ⟨((-67517119/2147483648), (220566277/4294967296)), (99/8589934592), by norm_num⟩
  | 7 => ⟨((218617603/17179869184), (-714184365/34359738368)), (81/17179869184), by norm_num⟩
  | 8 => ⟨((-309695155/68719476736), (1011718337/137438953472)), (29/17179869184), by norm_num⟩
  | 9 => ⟨((48746247/34359738368), (-636980865/274877906944)), (147/274877906944), by norm_num⟩
  | 10 => ⟨((-55243407/137438953472), (721881075/1099511627776)), (21/137438953472), by norm_num⟩
  | 11 => ⟨((227660157/2199023255552), (-371862381/2199023255552)), (175/4398046511104), by norm_num⟩
  | 12 => ⟨((-215003265/8796093022208), (702376973/17592186044416)), (167/17592186044416), by norm_num⟩
  | _ => zero

def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580746512500455/10141204801825835211973625643008), (2761731966523/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889070048994793/316912650057057350374175801344), (1633092316215/316912650057057350374175801344)), (46261/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889034467956361/39614081257132168796771975168), (1836829338749/19807040628566084398385987584)), (26027/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888765153613293/2475880078570760549798248448), (1951137216975/1237940039285380274899124224)), (110639/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770431205140273/154742504910672534362390528), (3901163360379/154742504910672534362390528)), (110665/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774420600332135/4835703278458516698824704), (3656160474511/9671406556917033397649408)), (51889/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((39317664911941/18889465931478580854784), (799490155357/151115727451828646838272)), (45417/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886778616706549/75557863725914323419136), (1298618677067/18889465931478580854784)), (147659/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296779038641581/4722366482869645213696), (973480488485/1180591620717411303424)), (13849/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1620401986977433/590295810358705651712), (5351001332507/590295810358705651712)), (76207/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822166123808745/73786976294838206464), (6684042296115/73786976294838206464)), (190633/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455295919632221/2305843009213693952), (7513076524001/9223372036854775808)), (53655/2305843009213693952), by norm_num⟩
  | 6 => ⟨((796215367849021/576460752303423488), (1876248545923/288230376151711744)), (214817/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596609202561385/72057594037927936), (6557786189029/144115188075855872)), (47047/36028797018963968), by norm_num⟩
  | 4 => ⟨((1489590635580525/36028797018963968), (9818534106571/36028797018963968)), (141363/18014398509481984), by norm_num⟩
  | 3 => ⟨((1486693610936243/9007199254740992), (12241463641467/9007199254740992)), (354189/9007199254740992), by norm_num⟩
  | 2 => ⟨((277850407498065/562949953421312), (12194007710821/2251799813685248)), (177681/1125899906842624), by norm_num⟩
  | 1 => ⟨((1104172670142935/1125899906842624), (36345443165725/2251799813685248)), (33499/70368744177664), by norm_num⟩
  | 0 => ⟨((2165054781498441/2251799813685248), (8968594858271/281474976710656)), (2167567/2251799813685248), by norm_num⟩
  | _ => zero

def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((2165054781498441/2251799813685248), (8968594858271/281474976710656)), (8268611916548918967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2079365267744405/2251799813685248), (68984814949225/1125899906842624)), (538283/281474976710656), by norm_num⟩
  | 2 => ⟨((1911681612088965/2251799813685248), (127404423195537/1125899906842624)), (4240355/1125899906842624), by norm_num⟩
  | 3 => ⟨((1594102200375109/2251799813685248), (54080449701057/281474976710656)), (8159419/1125899906842624), by norm_num⟩
  | 4 => ⟨((522688857238313/1125899906842624), (612557214663883/2251799813685248)), (29375735/2251799813685248), by norm_num⟩
  | 5 => ⟨((637346375398451/4503599627370496), (568748302721909/2251799813685248)), (43257005/2251799813685248), by norm_num⟩
  | 6 => ⟨((-788425436193543/18014398509481984), (643911003190975/9007199254740992)), (272757439/18014398509481984), by norm_num⟩
  | _ => zero

def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-41591753/16777216), (-1193831859/33554432)), (1/16777216), by norm_num⟩, -6, term17ValuePoly, term17ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term17Value_checks : CertifiedScalarExp.Checks term17Value := by
  constructor
  · norm_num [term17Value, CertifiedScalarExp.reduced, term17ValuePoly, term17ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term17Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term17ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term17Value, term17ValueSquares, term17ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term17Value, CertifiedScalarExp.roundingCheck, term17ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term17 : Sound J_term17 F_term17 c := by
  apply exp_sound (A_arg17 hcre) S_arg17 term17Value term17Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term17Value,J_arg17]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term17,J_arg17,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log18 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((722592939474041/250000000000000), 0), (3/500000000000000), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_log18 : Sound J_log18 F_log18 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log18_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog18 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-775878261/268435456), 0), (1/536870912), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_negLog18 : Sound J_negLog18 F_negLog18 c := by
  apply sound_round (sound_scale (A_log18 hcre) S_log18)
  intro k
  fin_cases k <;> norm_num [J_negLog18, J_log18, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg18 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-84861685/33554432), (-304479179/8388608)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-775878261/268435456), 0), (1/536870912), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_arg18 : Sound J_arg18 F_arg18 c := by
  apply sound_round (sound_mul (A_negLog18 hcre) (A_variable hcre) S_negLog18 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg18, J_negLog18, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term18 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((60195390777799/4503599627370496), (354002821310431/4503599627370496)), (860289/70368744177664), by norm_num⟩
  | 1 => ⟨((-41481747/1073741824), (-975799329/4294967296)), (153/4294967296), by norm_num⟩
  | 2 => ⟨((59948835/1073741824), (1410211411/4294967296)), (223/4294967296), by norm_num⟩
  | 3 => ⟨((-14439535/268435456), (-339669603/1073741824)), (217/4294967296), by norm_num⟩
  | 4 => ⟨((166942497/4294967296), (245442857/1073741824)), (159/4294967296), by norm_num⟩
  | 5 => ⟨((-193010351/8589934592), (-283768441/2147483648)), (93/4294967296), by norm_num⟩
  | 6 => ⟨((185957223/17179869184), (546797525/8589934592)), (181/17179869184), by norm_num⟩
  | 7 => ⟨((-307134575/68719476736), (-1806226427/68719476736)), (301/68719476736), by norm_num⟩
  | 8 => ⟨((221933275/137438953472), (10196613/1073741824)), (55/34359738368), by norm_num⟩
  | 9 => ⟨((-285097631/549755813888), (-1676629461/549755813888)), (285/549755813888), by norm_num⟩
  | 10 => ⟨((41201907/274877906944), (969216489/1099511627776)), (83/549755813888), by norm_num⟩
  | 11 => ⟨((-86610057/2199023255552), (-1018689443/4398046511104)), (11/274877906944), by norm_num⟩
  | 12 => ⟨((166890175/17592186044416), (245365933/4398046511104)), (171/17592186044416), by norm_num⟩
  | _ => zero

def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395170341040317/2535301200456458802993406410752), (1826737288897/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889033134651169/316912650057057350374175801344), (2160227178715/633825300114114700748351602688)), (92413/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944475803728227/19807040628566084398385987584), (1214860809645/19807040628566084398385987584)), (103979/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888677373766115/2475880078570760549798248448), (10081692159/9671406556917033397649408)), (110493/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770343716879673/154742504910672534362390528), (2580164217445/154742504910672534362390528)), (110511/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774379745004449/4835703278458516698824704), (302263555511/1208925819614629174706176)), (103623/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258094089698013/604462909807314587353088), (2115049689835/604462909807314587353088)), (90689/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886663516526125/75557863725914323419136), (429433176125/9444732965739290427392)), (147405/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296693220022657/4722366482869645213696), (2575295672257/4722366482869645213696)), (110585/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620284808473163/590295810358705651712), (110591087097/18446744073709551616)), (152105/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455505220522097/18446744073709551616), (552558813121/9223372036854775808)), (190207/73786976294838206464), by norm_num⟩
  | 7 => ⟨((113813873247843/576460752303423488), (4968669986973/9223372036854775808)), (214087/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796135568939813/576460752303423488), (4963226091285/1152921504606846976)), (107109/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193081123575425/144115188075855872), (1084176421077/36028797018963968)), (46897/36028797018963968), by norm_num⟩
  | 4 => ⟨((1489389431885799/36028797018963968), (6492842307943/36028797018963968)), (281677/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486450331443583/9007199254740992), (505919694419/562949953421312)), (176307/4503599627370496), by norm_num⟩
  | 2 => ⟨((138896327927041/281474976710656), (8062789527881/2251799813685248)), (706783/4503599627370496), by norm_num⟩
  | 1 => ⟨((2207713233253717/2251799813685248), (375457921563/35184372088832)), (1064077/2251799813685248), by norm_num⟩
  | 0 => ⟨((2164031518986457/2251799813685248), (47425755511965/2251799813685248)), (1071919/1125899906842624), by norm_num⟩
  | _ => zero

def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((2164031518986457/2251799813685248), (47425755511965/2251799813685248)), (4089046482566451671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2078685318487739/2251799813685248), (11394311021333/281474976710656)), (1052715/562949953421312), by norm_num⟩
  | 2 => ⟨((1915189568083705/2251799813685248), (84146687961805/1125899906842624)), (8115191/2251799813685248), by norm_num⟩
  | 3 => ⟨((1616319709770445/2251799813685248), (286272088653383/2251799813685248)), (15017199/2251799813685248), by norm_num⟩
  | 4 => ⟨((1123784485668387/2251799813685248), (205483283387593/1125899906842624)), (25376679/2251799813685248), by norm_num⟩
  | 5 => ⟨((971665460289353/4503599627370496), (820388826863825/4503599627370496)), (69183567/4503599627370496), by norm_num⟩
  | 6 => ⟨((60195390777799/4503599627370496), (354002821310431/4503599627370496)), (860289/70368744177664), by norm_num⟩
  | _ => zero

def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-84861685/33554432), (-304479179/8388608)), (1/16777216), by norm_num⟩, -6, term18ValuePoly, term18ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term18Value_checks : CertifiedScalarExp.Checks term18Value := by
  constructor
  · norm_num [term18Value, CertifiedScalarExp.reduced, term18ValuePoly, term18ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term18Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term18ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term18Value, term18ValueSquares, term18ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term18Value, CertifiedScalarExp.roundingCheck, term18ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term18 : Sound J_term18 F_term18 c := by
  apply exp_sound (A_arg18 hcre) S_arg18 term18Value term18Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term18Value,J_arg18]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term18,J_arg18,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log19 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((73610974479161/25000000000000), 0), (3/500000000000000), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_log19 : Sound J_log19 F_log19 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log19_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog19 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-197597955/67108864), 0), (1/536870912), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_negLog19 : Sound J_negLog19 F_negLog19 c := by
  apply sound_round (sound_scale (A_log19 hcre) S_log19)
  intro k
  fin_cases k <;> norm_num [J_negLog19, J_log19, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg19 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-86449105/33554432), (-1240699035/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-197597955/67108864), 0), (1/536870912), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_arg19 : Sound J_arg19 F_arg19 c := by
  apply sound_round (sound_mul (A_negLog19 hcre) (A_variable hcre) S_negLog19 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg19, J_negLog19, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term19 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((128359135711279/2251799813685248), (906831584022665/18014398509481984)), (151258367/18014398509481984), by norm_num⟩
  | 1 => ⟨((-720874105/4294967296), (-636603895/4294967296)), (27/1073741824), by norm_num⟩
  | 2 => ⟨((1061284907/4294967296), (937220661/4294967296)), (161/4294967296), by norm_num⟩
  | 3 => ⟨((-1041629549/4294967296), (-919863015/4294967296)), (161/4294967296), by norm_num⟩
  | 4 => ⟨((766753661/4294967296), (677120129/4294967296)), (121/4294967296), by norm_num⟩
  | 5 => ⟨((-903063747/8589934592), (-797495561/8589934592)), (145/8589934592), by norm_num⟩
  | 6 => ⟨((886338699/17179869184), (97840709/2147483648)), (9/1073741824), by norm_num⟩
  | 7 => ⟨((-745648633/34359738368), (-82310285/4294967296)), (123/34359738368), by norm_num⟩
  | 8 => ⟨((548879225/68719476736), (484715223/68719476736)), (183/137438953472), by norm_num⟩
  | 9 => ⟨((-179571265/68719476736), (-634317509/274877906944)), (61/137438953472), by norm_num⟩
  | 10 => ⟨((845978611/1099511627776), (747083679/1099511627776)), (73/549755813888), by norm_num⟩
  | 11 => ⟨((-905793599/4398046511104), (-799906293/4398046511104)), (79/2199023255552), by norm_num⟩
  | 12 => ⟨((889017993/17592186044416), (196272939/4398046511104)), (157/17592186044416), by norm_num⟩
  | _ => zero

def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395154934790955/2535301200456458802993406410752), (471154123329/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222249404111381/79228162514264337593543950336), (1114249347631/633825300114114700748351602688)), (46155/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888871810787813/39614081257132168796771975168), (156656448127/4951760157141521099596496896)), (6491/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((236074093388739/309485009821345068724781056), (1331230009195/2475880078570760549798248448)), (27589/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1770259267014335/154742504910672534362390528), (1330836672459/154742504910672534362390528)), (110365/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774340252983077/4835703278458516698824704), (1247241620379/9671406556917033397649408)), (103477/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629012583107715/302231454903657293676544), (34091213691/18889465931478580854784)), (11319/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((943275933605575/37778931862957161709568), (1771960532975/75557863725914323419136)), (147165/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296609790141815/4722366482869645213696), (166035753243/590295810358705651712)), (55195/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810085295416147/295147905179352825856), (1825281895565/590295810358705651712)), (37953/147573952589676412928), by norm_num⟩
  | 8 => ⟨((227734857081827/9223372036854775808), (2279936538655/73786976294838206464)), (189805/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820863218246065/9223372036854775808), (2562640125267/9223372036854775808)), (13349/576460752303423488), by norm_num⟩
  | 6 => ⟨((796056831361421/576460752303423488), (2559782576335/1152921504606846976)), (53413/288230376151711744), by norm_num⟩
  | 5 => ⟨((596472383844873/72057594037927936), (2236599203365/144115188075855872)), (93511/72057594037927936), by norm_num⟩
  | 4 => ⟨((744593879530653/18014398509481984), (1674244083877/18014398509481984)), (280687/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486203227531921/9007199254740992), (2087207549951/4503599627370496)), (351127/9007199254740992), by norm_num⟩
  | 2 => ⟨((1110930961024517/2251799813685248), (129927167089/70368744177664)), (87883/562949953421312), by norm_num⟩
  | 1 => ⟨((1103515590311615/1125899906842624), (1548700845591/281474976710656)), (1056633/2251799813685248), by norm_num⟩
  | 0 => ⟨((1081406760999615/1125899906842624), (24447566245311/2251799813685248)), (2121477/2251799813685248), by norm_num⟩
  | _ => zero

def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((1081406760999615/1125899906842624), (24447566245311/2251799813685248)), (8092792519576262717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((259634794077945/281474976710656), (46962901883179/2251799813685248)), (1030337/562949953421312), by norm_num⟩
  | 2 => ⟨((957467209691057/1125899906842624), (86637920729103/2251799813685248)), (3887519/1125899906842624), by norm_num⟩
  | 3 => ⟨((812565059954651/1125899906842624), (147354072435365/2251799813685248)), (13822101/2251799813685248), by norm_num⟩
  | 4 => ⟨((1163218270138493/2251799813685248), (212691678852303/2251799813685248)), (21759889/2251799813685248), by norm_num⟩
  | 5 => ⟨((1161594370674181/4503599627370496), (439482844334243/4503599627370496)), (53183499/4503599627370496), by norm_num⟩
  | 6 => ⟨((128359135711279/2251799813685248), (906831584022665/18014398509481984)), (151258367/18014398509481984), by norm_num⟩
  | _ => zero

def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-86449105/33554432), (-1240699035/33554432)), (1/16777216), by norm_num⟩, -6, term19ValuePoly, term19ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term19Value_checks : CertifiedScalarExp.Checks term19Value := by
  constructor
  · norm_num [term19Value, CertifiedScalarExp.reduced, term19ValuePoly, term19ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term19Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term19ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term19Value, term19ValueSquares, term19ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term19Value, CertifiedScalarExp.roundingCheck, term19ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term19 : Sound J_term19 F_term19 c := by
  apply exp_sound (A_arg19 hcre) S_arg19 term19Value term19Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term19Value,J_arg19]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term19,J_arg19,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log20 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2995732273553991/1000000000000000), 0), (3/500000000000000), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_log20 : Sound J_log20 F_log20 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log20_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog20 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-804160759/268435456), 0), (1/536870912), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_negLog20 : Sound J_negLog20 F_negLog20 c := by
  apply sound_round (sound_scale (A_log20 hcre) S_log20)
  intro k
  fin_cases k <;> norm_num [J_negLog20, J_log20, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg20 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-87955083/33554432), (-157789063/4194304)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-804160759/268435456), 0), (1/536870912), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_arg20 : Sound J_arg20 F_arg20 c := by
  apply sound_round (sound_mul (A_negLog20 hcre) (A_variable hcre) S_negLog20 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg20, J_negLog20, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term20 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((81607991933223/1125899906842624), (12964912426573/2251799813685248)), (43945525/18014398509481984), by norm_num⟩
  | 1 => ⟨((-466300383/2147483648), (-74080289/4294967296)), (65/8589934592), by norm_num⟩
  | 2 => ⟨((1396911107/4294967296), (27740589/1073741824)), (51/4294967296), by norm_num⟩
  | 3 => ⟨((-174365487/536870912), (-13850563/536870912)), (53/4294967296), by norm_num⟩
  | 4 => ⟨((522352317/2147483648), (82985157/4294967296)), (41/4294967296), by norm_num⟩
  | 5 => ⟨((-312965539/2147483648), (-99440525/8589934592)), (51/8589934592), by norm_num⟩
  | 6 => ⟨((156260161/2147483648), (99299063/17179869184)), (53/17179869184), by norm_num⟩
  | 7 => ⟨((-133746745/4294967296), (-42496201/17179869184)), (47/34359738368), by norm_num⟩
  | 8 => ⟨((801338881/68719476736), (127307241/137438953472)), (9/17179869184), by norm_num⟩
  | 9 => ⟨((-66683243/17179869184), (-42375379/137438953472)), (49/274877906944), by norm_num⟩
  | 10 => ⟨((319624229/274877906944), (12694529/137438953472)), (61/1099511627776), by norm_num⟩
  | 11 => ⟨((-43523119/137438953472), (-27657753/1099511627776)), (69/4398046511104), by norm_num⟩
  | 12 => ⟨((1390758531/17592186044416), (110473631/17592186044416)), (71/17592186044416), by norm_num⟩
  | _ => zero

def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790280637907115/5070602400912917605986812821504), (806679357/79228162514264337593543950336)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((444481690527251/158456325028528675187087900672), (15260829003/79228162514264337593543950336)), (46107/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944397417358955/19807040628566084398385987584), (17164556353/4951760157141521099596496896)), (51871/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888511030140241/2475880078570760549798248448), (145859741451/2475880078570760549798248448)), (55113/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221272203604743/19342813113834066795298816), (145815902823/154742504910672534362390528)), (55113/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193575506729735/1208925819614629174706176), (136655848999/9671406556917033397649408)), (25835/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1257958354202477/604462909807314587353088), (29881832241/151115727451828646838272)), (11303/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((235805431788175/9444732965739290427392), (194144693683/75557863725914323419136)), (36735/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296528617367635/4722366482869645213696), (145532250911/4722366482869645213696)), (55103/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620059200489019/590295810358705651712), (199982990775/590295810358705651712)), (9471/73786976294838206464), by norm_num⟩
  | 8 => ⟨((14232343372039/576460752303423488), (62448275771/18446744073709551616)), (11839/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1820707407106287/9223372036854775808), (140381114641/4611686018427387904)), (106555/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591958421801071/1152921504606846976), (70110954937/288230376151711744)), (53279/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192809571922321/144115188075855872), (245030619179/144115188075855872)), (23311/36028797018963968), by norm_num⟩
  | 4 => ⟨((744493120927753/18014398509481984), (183415849911/18014398509481984)), (69937/18014398509481984), by norm_num⟩
  | 3 => ⟨((23218024322661/140737488355328), (457292457969/9007199254740992)), (43715/2251799813685248), by norm_num⟩
  | 2 => ⟨((2221369224649391/4503599627370496), (910854326095/4503599627370496)), (87443/1125899906842624), by norm_num⟩
  | 1 => ⟨((275788579011467/281474976710656), (1356993090181/2251799813685248)), (524795/2251799813685248), by norm_num⟩
  | 0 => ⟨((2161433738793761/2251799813685248), (2677060149747/2251799813685248)), (525085/1125899906842624), by norm_num⟩
  | _ => zero

def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((2161433738793761/2251799813685248), (2677060149747/2251799813685248)), (2003040318015670421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2074690925966097/2251799813685248), (2569628122925/1125899906842624)), (2018551/2251799813685248), by norm_num⟩
  | 2 => ⟨((1911500303078429/2251799813685248), (2367521356623/562949953421312)), (3728791/2251799813685248), by norm_num⟩
  | 3 => ⟨((1622588164340995/2251799813685248), (4019467239695/562949953421312)), (6361931/2251799813685248), by norm_num⟩
  | 4 => ⟨((1169079878766343/2251799813685248), (11585292672019/1125899906842624)), (2314833/562949953421312), by norm_num⟩
  | 5 => ⟨((1213439026513845/4503599627370496), (48118424986671/4503599627370496)), (19609991/4503599627370496), by norm_num⟩
  | 6 => ⟨((81607991933223/1125899906842624), (12964912426573/2251799813685248)), (43945525/18014398509481984), by norm_num⟩
  | _ => zero

def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-87955083/33554432), (-157789063/4194304)), (1/33554432), by norm_num⟩, -6, term20ValuePoly, term20ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term20Value_checks : CertifiedScalarExp.Checks term20Value := by
  constructor
  · norm_num [term20Value, CertifiedScalarExp.reduced, term20ValuePoly, term20ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term20Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term20ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term20Value, term20ValueSquares, term20ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term20Value, CertifiedScalarExp.roundingCheck, term20ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term20 : Sound J_term20 F_term20 c := by
  apply exp_sound (A_arg20 hcre) S_arg20 term20Value term20Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term20Value,J_arg20]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term20,J_arg20,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log21 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3044522437723423/1000000000000000), 0), (3/500000000000000), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_log21 : Sound J_log21 F_log21 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log21_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog21 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-817257769/268435456), 0), (1/536870912), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_negLog21 : Sound J_negLog21 F_negLog21 c := by
  apply sound_round (sound_scale (A_log21 hcre) S_log21)
  intro k
  fin_cases k <;> norm_num [J_negLog21, J_log21, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg21 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-5586723/2097152), (-320717807/8388608)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-817257769/268435456), 0), (1/536870912), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_arg21 : Sound J_arg21 F_arg21 c := by
  apply sound_round (sound_mul (A_negLog21 hcre) (A_variable hcre) S_negLog21 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg21, J_negLog21, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term21 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((540362663147575/9007199254740992), (-319102484853159/9007199254740992)), (15295909/2251799813685248), by norm_num⟩
  | 1 => ⟨((-49029179/268435456), (463254297/4294967296)), (45/2147483648), by norm_num⟩
  | 2 => ⟨((1194163485/4294967296), (-705194051/4294967296)), (139/4294967296), by norm_num⟩
  | 3 => ⟨((-605942921/2147483648), (89457463/536870912)), (143/4294967296), by norm_num⟩
  | 4 => ⟨((461201705/2147483648), (-544710507/4294967296)), (111/4294967296), by norm_num⟩
  | 5 => ⟨((-70206947/536870912), (323903/4194304)), (69/4294967296), by norm_num⟩
  | 6 => ⟨((569991001/8589934592), (-673198047/17179869184)), (71/8589934592), by norm_num⟩
  | 7 => ⟨((-991628795/34359738368), (292795223/17179869184)), (63/17179869184), by norm_num⟩
  | 8 => ⟨((754759029/68719476736), (-445710813/68719476736)), (97/68719476736), by norm_num⟩
  | 9 => ⟨((-1021280355/274877906944), (301550349/137438953472)), (133/274877906944), by norm_num⟩
  | 10 => ⟨((1243724383/1099511627776), (-734461443/1099511627776)), (41/274877906944), by norm_num⟩
  | 11 => ⟨((-688463053/2199023255552), (203280395/1099511627776)), (23/549755813888), by norm_num⟩
  | 12 => ⟨((174670101/2199023255552), (-412594483/8796093022208)), (95/8796093022208), by norm_num⟩
  | _ => zero

def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790252832762771/5070602400912917605986812821504), (-694852231347/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777860657940473/633825300114114700748351602688), (-821521679903/633825300114114700748351602688)), (46141/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472180116249103/9903520314283042199192993792), (-230999962593/9903520314283042199192993792)), (51911/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944216003769127/1237940039285380274899124224), (-490741603807/1237940039285380274899124224)), (110317/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((13828895319447/1208925819614629174706176), (-981183397963/154742504910672534362390528)), (27581/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((774264979735041/4835703278458516698824704), (-114942626969/1208925819614629174706176)), (25859/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((628946757990873/302231454903657293676544), (-804280112923/604462909807314587353088)), (45257/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943169040820507/37778931862957161709568), (-1306358722053/75557863725914323419136)), (73549/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296449578669069/4722366482869645213696), (-122405930423/590295810358705651712)), (431/18446744073709551616), by norm_num⟩
  | 9 => ⟨((809975253697691/295147905179352825856), (-1345618210279/590295810358705651712)), (75865/295147905179352825856), by norm_num⟩
  | 8 => ⟨((910802031523479/36893488147419103232), (-840376613811/36893488147419103232)), (47423/18446744073709551616), by norm_num⟩
  | 7 => ⟨((227569312764599/1152921504606846976), (-1889103395857/9223372036854775808)), (53361/2305843009213693952), by norm_num⟩
  | 6 => ⟨((795902739583869/576460752303423488), (-471731462597/288230376151711744)), (106747/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192675705160897/144115188075855872), (-1648613725905/144115188075855872)), (186865/144115188075855872), by norm_num⟩
  | 4 => ⟨((744392679388145/18014398509481984), (-2468036153869/36028797018963968)), (140205/18014398509481984), by norm_num⟩
  | 3 => ⟨((1485702309853175/9007199254740992), (-3076516187957/9007199254740992)), (350713/9007199254740992), by norm_num⟩
  | 2 => ⟨((2220866310940769/4503599627370496), (-6127520221703/4503599627370496)), (175507/1125899906842624), by norm_num⟩
  | 1 => ⟨((2205553241631131/2251799813685248), (-9127761196855/2251799813685248)), (527281/1125899906842624), by norm_num⟩
  | 0 => ⟨((1079959529641871/1125899906842624), (-2250375914399/281474976710656)), (528817/562949953421312), by norm_num⟩
  | _ => zero

def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((1079959529641871/1125899906842624), (-2250375914399/281474976710656)), (2017276766063499273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1035821702718381/1125899906842624), (-17268426077747/1125899906842624)), (1022935/562949953421312), by norm_num⟩
  | 2 => ⟨((1905370796754375/2251799813685248), (-63547426887277/2251799813685248)), (7654271/2251799813685248), by norm_num⟩
  | 3 => ⟨((402611232981399/562949953421312), (-107541896632225/2251799813685248)), (13385413/2251799813685248), by norm_num⟩
  | 4 => ⟨((71663997492743/140737488355328), (-9613993068371/140737488355328)), (2553065/281474976710656), by norm_num⟩
  | 5 => ⟨((1146713583221115/4503599627370496), (-78327636304833/1125899906842624)), (1474433/140737488355328), by norm_num⟩
  | 6 => ⟨((540362663147575/9007199254740992), (-319102484853159/9007199254740992)), (15295909/2251799813685248), by norm_num⟩
  | _ => zero

def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-5586723/2097152), (-320717807/8388608)), (1/16777216), by norm_num⟩, -6, term21ValuePoly, term21ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term21Value_checks : CertifiedScalarExp.Checks term21Value := by
  constructor
  · norm_num [term21Value, CertifiedScalarExp.reduced, term21ValuePoly, term21ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term21Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term21ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term21Value, term21ValueSquares, term21ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term21Value, CertifiedScalarExp.roundingCheck, term21ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term21 : Sound J_term21 F_term21 c := by
  apply exp_sound (A_arg21 hcre) S_arg21 term21Value term21Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term21Value,J_arg21]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term21,J_arg21,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term16Jet : Jet 12 := J_term16
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨32,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 12 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨32,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 12 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨32,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 12 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨32,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 12 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨32,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 12 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨32,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiRectangle.Tile032Terms2
