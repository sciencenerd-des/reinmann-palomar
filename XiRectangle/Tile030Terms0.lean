/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 32 bits, checked against fixed final error disks.
module

public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile030Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨30,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((7/8), (1551/128)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((7/8), (1551/128))
  have he : value ((7/8), (1551/128))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_log2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((138629436111989/200000000000000), 0), (1/1000000000000000), by norm_num⟩
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

theorem S_log2 : Sound J_log2 F_log2 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log2_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-372130559/536870912), 0), (1/8589934592), by norm_num⟩
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
theorem S_negLog2 : Sound J_negLog2 F_negLog2 c := by
  apply sound_round (sound_scale (A_log2 hcre) S_log2)
  intro k
  fin_cases k <;> norm_num [J_negLog2, J_log2, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-325614239/536870912), (-2254587879/268435456)), (1/268435456), by norm_num⟩
  | 1 => ⟨((-372130559/536870912), 0), (1/8589934592), by norm_num⟩
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
theorem S_arg2 : Sound J_arg2 F_arg2 c := by
  apply sound_round (sound_mul (A_negLog2 hcre) (A_variable hcre) S_negLog2 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg2, J_negLog2, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-79566051207719/281474976710656), (-1049919376625385/2251799813685248)), (13453017/2251799813685248), by norm_num⟩
  | 1 => ⟨((1683074465/8589934592), (2776140807/8589934592)), (37/8589934592), by norm_num⟩
  | 2 => ⟨((-72913645/1073741824), (-3848548347/34359738368)), (53/34359738368), by norm_num⟩
  | 3 => ⟨((539092133/34359738368), (3556813915/137438953472)), (51/137438953472), by norm_num⟩
  | 4 => ⟨((-2989361537/1099511627776), (-2465395537/549755813888)), (73/1099511627776), by norm_num⟩
  | 5 => ⟨((1657654017/4398046511104), (2734211145/4398046511104)), (21/2199023255552), by norm_num⟩
  | 6 => ⟨((-1531997611/35184372088832), (-1263473831/17592186044416)), (5/4398046511104), by norm_num⟩
  | 7 => ⟨((2427199599/562949953421312), (2001767597/281474976710656)), (33/281474976710656), by norm_num⟩
  | 8 => ⟨((-1682406559/4503599627370496), (-693759783/1125899906842624)), (47/4503599627370496), by norm_num⟩
  | 9 => ⟨((1036582545/36028797018963968), (427446789/9007199254740992)), (15/18014398509481984), by norm_num⟩
  | 10 => ⟨((-2299213659/1152921504606846976), (-3792429269/1152921504606846976)), (69/1152921504606846976), by norm_num⟩
  | 11 => ⟨((1159049793/9223372036854775808), (1911790295/9223372036854775808)), (71/18446744073709551616), by norm_num⟩
  | 12 => ⟨((-2142378923/295147905179352825856), (-441717351/36893488147419103232)), (17/73786976294838206464), by norm_num⟩
  | _ => zero

def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791592864105897/5070602400912917605986812821504), (-2756077513057/10141204801825835211973625643008)), (2427/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1781029340076799/633825300114114700748351602688), (-3269577258791/633825300114114700748351602688)), (5783/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1892284394632641/39614081257132168796771975168), (-459757687627/4951760157141521099596496896)), (1627/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((946108827743031/1237940039285380274899124224), (-3907696953699/2475880078570760549798248448)), (1729/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1773883093405217/154742504910672534362390528), (-976855761359/38685626227668133590597632)), (6917/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1552076693839687/9671406556917033397649408), (-3662917995907/9671406556917033397649408)), (6487/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157624460188551/75557863725914323419136), (-100148813919/18889465931478580854784)), (2839/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1891376800583561/75557863725914323419136), (-325449507929/4722366482869645213696)), (4615/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1300226606016717/4722366482869645213696), (-1952457988955/2361183241434822606848)), (6925/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1625140651990999/590295810358705651712), (-5368482163835/590295810358705651712)), (9527/590295810358705651712), by norm_num⟩
  | 8 => ⟨((914043421995823/36893488147419103232), (-6709436107293/73786976294838206464)), (11915/73786976294838206464), by norm_num⟩
  | 7 => ⟨((913920448523523/4611686018427387904), (-3773255255935/4611686018427387904)), (6707/4611686018427387904), by norm_num⟩
  | 6 => ⟨((799541731221935/576460752303423488), (-7544502571317/1152921504606846976)), (13427/1152921504606846976), by norm_num⟩
  | 5 => ⟨((599517242410051/72057594037927936), (-6599178681605/144115188075855872)), (5881/72057594037927936), by norm_num⟩
  | 4 => ⟨((749152317674983/18014398509481984), (-9894240554695/36028797018963968)), (8835/18014398509481984), by norm_num⟩
  | 3 => ⟨((374392096142091/2251799813685248), (-6179932824311/4503599627370496)), (2767/1125899906842624), by norm_num⟩
  | 2 => ⟨((1122249781820071/2251799813685248), (-12347939175927/2251799813685248)), (22209/2251799813685248), by norm_num⟩
  | 1 => ⟨((1120378230129225/1125899906842624), (-18492009123851/1125899906842624)), (33495/1125899906842624), by norm_num⟩
  | 0 => ⟨((1114671169422205/1125899906842624), (-9215980156997/281474976710656)), (67717/1125899906842624), by norm_num⟩
  | _ => zero

def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((1114671169422205/1125899906842624), (-9215980156997/281474976710656)), (258319859031295421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((551173714356867/562949953421312), (-18248136120341/281474976710656)), (138519/1125899906842624), by norm_num⟩
  | 2 => ⟨((134319438021215/140737488355328), (-71465627837157/562949953421312)), (72301/281474976710656), by norm_num⟩
  | 3 => ⟨((1007407657465369/1125899906842624), (-272826325980311/1125899906842624)), (156365/281474976710656), by norm_num⟩
  | 4 => ⟨((208818736562743/281474976710656), (-244113467174419/562949953421312)), (177799/140737488355328), by norm_num⟩
  | 5 => ⟨((203978476958477/562949953421312), (-362202469214259/562949953421312)), (3344061/1125899906842624), by norm_num⟩
  | 6 => ⟨((-79566051207719/281474976710656), (-1049919376625385/2251799813685248)), (13453017/2251799813685248), by norm_num⟩
  | _ => zero

def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-325614239/536870912), (-2254587879/268435456)), (1/268435456), by norm_num⟩, -1, term2ValuePoly, term2ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term2Value_checks : CertifiedScalarExp.Checks term2Value := by
  constructor
  · norm_num [term2Value, CertifiedScalarExp.reduced, term2ValuePoly, term2ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term2Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term2ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term2Value, term2ValueSquares, term2ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term2Value, CertifiedScalarExp.roundingCheck, term2ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term2 : Sound J_term2 F_term2 c := by
  apply exp_sound (A_arg2 hcre) S_arg2 term2Value term2Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term2Value,J_arg2]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term2,J_arg2,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((109861228866811/100000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log3 : Sound J_log3 F_log3 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log3_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-4718503851/4294967296), 0), (1/4294967296), by norm_num⟩
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
theorem S_negLog3 : Sound J_negLog3 F_negLog3 c := by
  apply sound_round (sound_scale (A_log3 hcre) S_log3)
  intro k
  fin_cases k <;> norm_num [J_negLog3, J_log3, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-516086359/536870912), (-7146874485/536870912)), (3/536870912), by norm_num⟩
  | 1 => ⟨((-4718503851/4294967296), 0), (1/4294967296), by norm_num⟩
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
theorem S_arg3 : Sound J_arg3 F_arg3 c := by
  apply sound_round (sound_mul (A_negLog3 hcre) (A_variable hcre) S_negLog3 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg3, J_negLog3, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((632556263400525/2251799813685248), (-146062705442795/562949953421312)), (8809231/2251799813685248), by norm_num⟩
  | 1 => ⟨((-2650963151/8589934592), (1224260583/4294967296)), (39/8589934592), by norm_num⟩
  | 2 => ⟨((2912380695/17179869184), (-1344987721/8589934592)), (45/17179869184), by norm_num⟩
  | 3 => ⟨((-4266102961/68719476736), (3940320103/68719476736)), (69/68719476736), by norm_num⟩
  | 4 => ⟨((2343396569/137438953472), (-2164442043/137438953472)), (5/17179869184), by norm_num⟩
  | 5 => ⟨((-4119174829/1099511627776), (3804612203/1099511627776)), (73/1099511627776), by norm_num⟩
  | 6 => ⟨((3016917391/4398046511104), (-2786529147/4398046511104)), (7/549755813888), by norm_num⟩
  | 7 => ⟨((-3787911451/35184372088832), (3498645901/35184372088832)), (73/35184372088832), by norm_num⟩
  | 8 => ⟨((4161446069/281474976710656), (-3843655381/281474976710656)), (83/281474976710656), by norm_num⟩
  | 9 => ⟨((-2031918129/1125899906842624), (3753499587/2251799813685248)), (83/2251799813685248), by norm_num⟩
  | 10 => ⟨((1785832181/9007199254740992), (-1649456309/9007199254740992)), (75/18014398509481984), by norm_num⟩
  | 11 => ⟨((-2853726807/144115188075855872), (2635800685/144115188075855872)), (31/72057594037927936), by norm_num⟩
  | 12 => ⟨((4180185785/2305843009213693952), (-3860964031/2305843009213693952)), (93/2305843009213693952), by norm_num⟩
  | _ => zero

def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582723585083759/10141204801825835211973625643008), (-30355755681/316912650057057350374175801344)), (455/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((1780486239932391/633825300114114700748351602688), (-575847465581/316912650057057350374175801344)), (8655/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891673753943673/39614081257132168796771975168), (-1295544863983/39614081257132168796771975168)), (4869/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((945784635641275/1237940039285380274899124224), (-688190657151/1237940039285380274899124224)), (10347/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1773235183365299/154742504910672534362390528), (-1376229339899/154742504910672534362390528)), (2587/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1551469781892625/9671406556917033397649408), (-645026776185/4835703278458516698824704)), (9703/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((630232568588121/302231454903657293676544), (-1128635425929/604462909807314587353088)), (4245/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1890515610134645/75557863725914323419136), (-916864963423/37778931862957161709568)), (6899/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((649790769529995/2361183241434822606848), (-1375032680329/4722366482869645213696)), (10351/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((812127513303089/295147905179352825856), (-1890239777847/590295810358705651712)), (7117/295147905179352825856), by norm_num⟩
  | 8 => ⟨((913490912063223/36893488147419103232), (-1181077317491/36893488147419103232)), (4449/18446744073709551616), by norm_num⟩
  | 7 => ⟨((114162532184317/576460752303423488), (-2656537211499/9223372036854775808)), (10013/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1597846535310367/1152921504606846976), (-1327714566845/576460752303423488)), (313/18014398509481984), by norm_num⟩
  | 5 => ⟨((1197956058214093/144115188075855872), (-1161127201905/72057594037927936)), (137/1125899906842624), by norm_num⟩
  | 4 => ⟨((1496694759210657/36028797018963968), (-3480890677455/36028797018963968)), (13159/18014398509481984), by norm_num⟩
  | 3 => ⟨((373892403400335/2251799813685248), (-4346757029599/9007199254740992)), (16461/4503599627370496), by norm_num⟩
  | 2 => ⟨((140033918419701/281474976710656), (-8680456331781/4503599627370496)), (515/35184372088832), by norm_num⟩
  | 1 => ⟨((2234922665514543/2251799813685248), (-12988079442857/2251799813685248)), (387/8796093022208), by norm_num⟩
  | 0 => ⟨((2218079738769473/2251799813685248), (-25845974079703/2251799813685248)), (777/8796093022208), by norm_num⟩
  | _ => zero

def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((2218079738769473/2251799813685248), (-25845974079703/2251799813685248)), (2964019808945057/33554432000000000000000000), by norm_num⟩
  | 1 => ⟨((2184567954605543/2251799813685248), (-50917875635781/2251799813685248)), (198217/1125899906842624), by norm_num⟩
  | 2 => ⟨((1059096037143755/1125899906842624), (-98795247032617/2251799813685248)), (787125/2251799813685248), by norm_num⟩
  | 3 => ⟨((1988177250717177/2251799813685248), (-185866708017249/2251799813685248)), (1549913/2251799813685248), by norm_num⟩
  | 4 => ⟨((870037896643115/1125899906842624), (-328213865459747/2251799813685248)), (748197/562949953421312), by norm_num⟩
  | 5 => ⟨((324200602464039/562949953421312), (-126813449143317/562949953421312)), (687223/281474976710656), by norm_num⟩
  | 6 => ⟨((632556263400525/2251799813685248), (-146062705442795/562949953421312)), (8809231/2251799813685248), by norm_num⟩
  | _ => zero

def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-516086359/536870912), (-7146874485/536870912)), (3/536870912), by norm_num⟩, -2, term3ValuePoly, term3ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term3Value_checks : CertifiedScalarExp.Checks term3Value := by
  constructor
  · norm_num [term3Value, CertifiedScalarExp.reduced, term3ValuePoly, term3ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term3Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term3ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term3Value, term3ValueSquares, term3ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term3Value, CertifiedScalarExp.roundingCheck, term3ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term3 : Sound J_term3 F_term3 c := by
  apply exp_sound (A_arg3 hcre) S_arg3 term3Value term3Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term3Value,J_arg3]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term3,J_arg3,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((138629436111989/100000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log4 : Sound J_log4 F_log4 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log4_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-372130559/268435456), 0), (1/4294967296), by norm_num⟩
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
theorem S_negLog4 : Sound J_negLog4 F_negLog4 c := by
  apply sound_round (sound_scale (A_log4 hcre) S_log4)
  intro k
  fin_cases k <;> norm_num [J_negLog4, J_log4, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-325614239/268435456), (-2254587879/134217728)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-372130559/268435456), 0), (1/4294967296), by norm_num⟩
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
theorem S_arg4 : Sound J_arg4 F_arg4 c := by
  apply sound_round (sound_mul (A_negLog4 hcre) (A_variable hcre) S_negLog4 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg4, J_negLog4, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-309602246554097/2251799813685248), (296786378173955/1125899906842624)), (7351151/1125899906842624), by norm_num⟩
  | 1 => ⟨((1637267489/8589934592), (-784746709/2147483648)), (79/8589934592), by norm_num⟩
  | 2 => ⟨((-70929209/536870912), (4351559751/17179869184)), (7/1073741824), by norm_num⟩
  | 3 => ⟨((1048840133/17179869184), (-1005423791/8589934592)), (53/17179869184), by norm_num⟩
  | 4 => ⟨((-727000581/34359738368), (348453333/8589934592)), (75/68719476736), by norm_num⟩
  | 5 => ⟨((806269445/137438953472), (-772894225/68719476736)), (85/274877906944), by norm_num⟩
  | 6 => ⟨((-372575595/274877906944), (2857223749/1099511627776)), (5/68719476736), by norm_num⟩
  | 7 => ⟨((2361140327/8796093022208), (-4526803625/8796093022208)), (129/8796093022208), by norm_num⟩
  | 8 => ⟨((-1636617761/35184372088832), (1568870585/17592186044416)), (91/35184372088832), by norm_num⟩
  | 9 => ⟨((1008370655/140737488355328), (-3866518125/281474976710656)), (57/140737488355328), by norm_num⟩
  | 10 => ⟨((-2236637685/2251799813685248), (4288105819/2251799813685248)), (129/2251799813685248), by norm_num⟩
  | 11 => ⟨((281876201/2251799813685248), (-4323328667/18014398509481984)), (33/4503599627370496), by norm_num⟩
  | 12 => ⟨((-2084071403/144115188075855872), (1997802051/72057594037927936)), (31/36028797018963968), by norm_num⟩
  | _ => zero

def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582395689318205/10141204801825835211973625643008), (668098839443/2535301200456458802993406410752)), (9707/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1780092913245897/633825300114114700748351602688), (1583569083729/316912650057057350374175801344)), (11565/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891231030438415/39614081257132168796771975168), (3562635253955/39614081257132168796771975168)), (13013/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1891098586331153/2475880078570760549798248448), (3784830153119/2475880078570760549798248448)), (13829/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886382085462633/77371252455336267181195264), (3784301596399/154742504910672534362390528)), (1729/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1551027859920723/9671406556917033397649408), (3547221160801/9671406556917033397649408)), (12971/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1260078107807105/604462909807314587353088), (1551628468127/302231454903657293676544)), (11353/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889886035929753/75557863725914323419136), (5041739573611/75557863725914323419136)), (18455/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649554394356573/2361183241434822606848), (59068490073/73786976294838206464)), (13847/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1623604069787445/590295810358705651712), (5196530014807/590295810358705651712)), (19049/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1826166741619263/73786976294838206464), (6493416897353/73786976294838206464)), (1489/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1825681642587917/9223372036854775808), (7302006356643/9223372036854775808)), (13411/4611686018427387904), by norm_num⟩
  | 6 => ⟨((798462642542189/576460752303423488), (7298146906641/1152921504606846976)), (13423/576460752303423488), by norm_num⟩
  | 5 => ⟨((598573646515853/72057594037927936), (3190768412295/72057594037927936)), (23517/144115188075855872), by norm_num⟩
  | 4 => ⟨((1495476278620991/36028797018963968), (4781811107227/18014398509481984)), (69/70368744177664), by norm_num⟩
  | 3 => ⟨((1494037202142011/9007199254740992), (2984833359107/2251799813685248)), (22127/4503599627370496), by norm_num⟩
  | 2 => ⟨((1118725013192119/2251799813685248), (5958271956863/1125899906842624)), (44395/2251799813685248), by norm_num⟩
  | 1 => ⟨((1115107176407951/1125899906842624), (17817849242865/1125899906842624)), (66945/1125899906842624), by norm_num⟩
  | 0 => ⟨((1104193845017719/1125899906842624), (35407877183371/1125899906842624)), (67653/562949953421312), by norm_num⟩
  | _ => zero

def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((1104193845017719/1125899906842624), (35407877183371/1125899906842624)), (258075716258811773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1081792726161607/1125899906842624), (34725253828879/562949953421312)), (136953/562949953421312), by norm_num⟩
  | 2 => ⟨((1035129430493101/1125899906842624), (133459561646265/1125899906842624)), (35009/70368744177664), by norm_num⟩
  | 3 => ⟨((935857154685279/1125899906842624), (122700001306659/562949953421312)), (1162765/1125899906842624), by norm_num⟩
  | 4 => ⟨((362202469214261/562949953421312), (101989238479243/281474976710656)), (1219935/562949953421312), by norm_num⟩
  | 5 => ⟨((79566051207717/281474976710656), (524959688312719/1125899906842624)), (9815495/2251799813685248), by norm_num⟩
  | 6 => ⟨((-309602246554097/2251799813685248), (296786378173955/1125899906842624)), (7351151/1125899906842624), by norm_num⟩
  | _ => zero

def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-325614239/268435456), (-2254587879/134217728)), (1/134217728), by norm_num⟩, -3, term4ValuePoly, term4ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term4Value_checks : CertifiedScalarExp.Checks term4Value := by
  constructor
  · norm_num [term4Value, CertifiedScalarExp.reduced, term4ValuePoly, term4ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term4Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term4ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term4Value, term4ValueSquares, term4ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term4Value, CertifiedScalarExp.roundingCheck, term4ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term4 : Sound J_term4 F_term4 c := by
  apply exp_sound (A_arg4 hcre) S_arg4 term4Value term4Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term4Value,J_arg4]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term4,J_arg4,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((16094379124341/10000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log5 : Sound J_log5 F_log5 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log5_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-6912483199/4294967296), 0), (1/4294967296), by norm_num⟩
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
theorem S_negLog5 : Sound J_negLog5 F_negLog5 c := by
  apply sound_round (sound_scale (A_log5 hcre) S_log5)
  intro k
  fin_cases k <;> norm_num [J_negLog5, J_log5, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-378026425/268435456), (-2617495469/134217728)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-6912483199/4294967296), 0), (1/4294967296), by norm_num⟩
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
theorem S_arg5 : Sound J_arg5 F_arg5 c := by
  apply sound_round (sound_mul (A_negLog5 hcre) (A_variable hcre) S_negLog5 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg5, J_negLog5, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((437650042992641/2251799813685248), (-334298077374885/2251799813685248)), (14264265/4503599627370496), by norm_num⟩
  | 1 => ⟨((-2686960493/8589934592), (1026214599/4294967296)), (23/4294967296), by norm_num⟩
  | 2 => ⟨((4324496087/17179869184), (-825814341/4294967296)), (19/4294967296), by norm_num⟩
  | 3 => ⟨((-4640005303/34359738368), (443032303/4294967296)), (21/8589934592), by norm_num⟩
  | 4 => ⟨((58342191/1073741824), (-713032985/17179869184)), (35/34359738368), by norm_num⟩
  | 5 => ⟨((-2403792233/137438953472), (918065855/68719476736)), (93/274877906944), by norm_num⟩
  | 6 => ⟨((2579169569/549755813888), (-492523331/137438953472)), (51/549755813888), by norm_num⟩
  | 7 => ⟨((-4744015185/4398046511104), (905926539/1099511627776)), (3/137438953472), by norm_num⟩
  | 8 => ⟨((954399737/4398046511104), (-729016259/4398046511104)), (79/17592186044416), by norm_num⟩
  | 9 => ⟨((-682687609/17592186044416), (2085878055/70368744177664)), (29/35184372088832), by norm_num⟩
  | 10 => ⟨((3515978625/562949953421312), (-1342836489/281474976710656)), (19/140737488355328), by norm_num⟩
  | 11 => ⟨((-4115454035/4503599627370496), (1571790513/2251799813685248)), (91/4503599627370496), by norm_num⟩
  | 12 => ⟨((2207855917/18014398509481984), (-3372932323/36028797018963968)), (25/9007199254740992), by norm_num⟩
  | _ => zero

def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582141353601407/10141204801825835211973625643008), (-849700134843/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889898176732765/316912650057057350374175801344), (-503340903149/316912650057057350374175801344)), (5769/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((236362215516509/4951760157141521099596496896), (-1132375439457/39614081257132168796771975168)), (12981/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((59085776614603/77371252455336267181195264), (-300744000025/618970019642690137449562112)), (6897/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((886205444899681/77371252455336267181195264), (-601390762113/77371252455336267181195264)), (6897/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387674285145567/2417851639229258349412352), (-1127401089705/9671406556917033397649408)), (12933/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259789209915243/604462909807314587353088), (-493134705381/302231454903657293676544)), (5659/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1889417479323895/75557863725914323419136), (-1602300623715/75557863725914323419136)), (18393/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298758160519703/4722366482869645213696), (-1201386793929/4722366482869645213696)), (13797/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1623123237822707/590295810358705651712), (-1651356681861/590295810358705651712)), (18973/590295810358705651712), by norm_num⟩
  | 8 => ⟨((456391905764223/18446744073709551616), (-2063370936673/73786976294838206464)), (23721/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1825010273995993/9223372036854775808), (-2320158571073/9223372036854775808)), (6673/2305843009213693952), by norm_num⟩
  | 6 => ⟨((798128606521945/576460752303423488), (-1159371097175/576460752303423488)), (6675/288230376151711744), by norm_num⟩
  | 5 => ⟨((1196566434236307/144115188075855872), (-2027307080687/144115188075855872)), (11685/72057594037927936), by norm_num⟩
  | 4 => ⟨((747306193981221/18014398509481984), (-3037778651567/36028797018963968)), (35073/36028797018963968), by norm_num⟩
  | 3 => ⟨((1492970259891589/9007199254740992), (-3791660958723/9007199254740992)), (43871/9007199254740992), by norm_num⟩
  | 2 => ⟨((139709675420279/281474976710656), (-7566659188341/4503599627370496)), (43915/2251799813685248), by norm_num⟩
  | 1 => ⟨((2227167841440207/2251799813685248), (-176694016091/35184372088832)), (65985/1125899906842624), by norm_num⟩
  | 0 => ⟨((1101338939232809/1125899906842624), (-22451056564049/2251799813685248)), (264843/2251799813685248), by norm_num⟩
  | _ => zero

def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((1101338939232809/1125899906842624), (-22451056564049/2251799813685248)), (1010295876509856467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1077201835806497/1125899906842624), (-21961297510225/1125899906842624)), (523413/2251799813685248), by norm_num⟩
  | 2 => ⟨((2060363429159925/2251799813685248), (-84045659302159/2251799813685248)), (63873/140737488355328), by norm_num⟩
  | 3 => ⟨((1882065075951949/2251799813685248), (-76900531634029/1125899906842624)), (1946459/2251799813685248), by norm_num⟩
  | 4 => ⟨((1562534183399413/2251799813685248), (-64273832882897/562949953421312)), (3519613/2251799813685248), by norm_num⟩
  | 5 => ⟨((1054896199191339/2251799813685248), (-356799251397987/2251799813685248)), (5688243/2251799813685248), by norm_num⟩
  | 6 => ⟨((437650042992641/2251799813685248), (-334298077374885/2251799813685248)), (14264265/4503599627370496), by norm_num⟩
  | _ => zero

def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-378026425/268435456), (-2617495469/134217728)), (1/134217728), by norm_num⟩, -3, term5ValuePoly, term5ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term5Value_checks : CertifiedScalarExp.Checks term5Value := by
  constructor
  · norm_num [term5Value, CertifiedScalarExp.reduced, term5ValuePoly, term5ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term5Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term5ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term5Value, term5ValueSquares, term5ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term5Value, CertifiedScalarExp.roundingCheck, term5ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term5 : Sound J_term5 F_term5 c := by
  apply exp_sound (A_arg5 hcre) S_arg5 term5Value term5Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term5Value,J_arg5]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term5,J_arg5,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((358351893845611/200000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log6 : Sound J_log6 F_log6 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log6_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-7695548323/4294967296), 0), (1/4294967296), by norm_num⟩
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
theorem S_negLog6 : Sound J_negLog6 F_negLog6 c := by
  apply sound_round (sound_scale (A_log6 hcre) S_log6)
  intro k
  fin_cases k <;> norm_num [J_negLog6, J_log6, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-420850299/268435456), (-2914012561/134217728)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-7695548323/4294967296), 0), (1/4294967296), by norm_num⟩
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
theorem S_arg6 : Sound J_arg6 F_arg6 c := by
  apply sound_round (sound_mul (A_negLog6 hcre) (A_variable hcre) S_negLog6 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg6, J_negLog6, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-902439271306549/4503599627370496), (-129780999028337/2251799813685248)), (5057197/1125899906842624), by norm_num⟩
  | 1 => ⟨((6168190421/17179869184), (1774111435/17179869184)), (141/17179869184), by norm_num⟩
  | 2 => ⟨((-2762978399/8589934592), (-794695241/8589934592)), (1/134217728), by norm_num⟩
  | 3 => ⟨((825098785/4294967296), (474634241/8589934592)), (155/34359738368), by norm_num⟩
  | 4 => ⟨((-5913514245/68719476736), (-212607599/8589934592)), (141/68719476736), by norm_num⟩
  | 5 => ⟨((2119119029/68719476736), (304753343/34359738368)), (51/68719476736), by norm_num⟩
  | 6 => ⟨((-1265650529/137438953472), (-11375931/4294967296)), (31/137438953472), by norm_num⟩
  | 7 => ⟨((1295852183/549755813888), (745432945/1099511627776)), (129/2199023255552), by norm_num⟩
  | 8 => ⟨((-4643710839/8796093022208), (-667818269/4398046511104)), (117/8796093022208), by norm_num⟩
  | 9 => ⟨((3697961275/35184372088832), (531808759/17592186044416)), (95/35184372088832), by norm_num⟩
  | 10 => ⟨((-5300685705/281474976710656), (-47643669/8796093022208)), (69/140737488355328), by norm_num⟩
  | 11 => ⟨((3453655929/1125899906842624), (993349761/1125899906842624)), (91/1125899906842624), by norm_num⟩
  | 12 => ⟨((-2062706905/4503599627370496), (-2317505/17592186044416)), (111/9007199254740992), by norm_num⟩
  | _ => zero

def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790966773095085/5070602400912917605986812821504), (-3727461697275/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889770155568059/316912650057057350374175801344), (-2207473473143/316912650057057350374175801344)), (2895/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((945304570682283/19807040628566084398385987584), (-1241524763911/9903520314283042199192993792)), (13031/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890437549872537/2475880078570760549798248448), (-5275632890073/2475880078570760549798248448)), (6925/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1772102820473687/154742504910672534362390528), (-5274679474031/154742504910672534362390528)), (6927/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1550407510497655/9671406556917033397649408), (-2471999489355/4835703278458516698824704)), (12993/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629767484480051/302231454903657293676544), (-2162493025707/302231454903657293676544)), (5687/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((944501405658619/37778931862957161709568), (-7026202799065/75557863725914323419136)), (18491/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298445824845517/4722366482869645213696), (-2633994975335/2361183241434822606848)), (13877/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202836451158443/73786976294838206464), (-905098135845/73786976294838206464)), (19093/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912512420033621/36893488147419103232), (-4523464767787/36893488147419103232)), (23885/73786976294838206464), by norm_num⟩
  | 7 => ⟨((114024698957121/576460752303423488), (-2543056045701/2305843009213693952)), (26897/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595636555404621/1152921504606846976), (-2541314831559/288230376151711744)), (13465/576460752303423488), by norm_num⟩
  | 5 => ⟨((1196017106717169/144115188075855872), (-2221691468107/36028797018963968)), (11801/72057594037927936), by norm_num⟩
  | 4 => ⟨((746887959676969/18014398509481984), (-13314475329307/36028797018963968)), (35477/36028797018963968), by norm_num⟩
  | 3 => ⟨((46621965598459/281474976710656), (-8307831252597/4503599627370496)), (44477/9007199254740992), by norm_num⟩
  | 2 => ⟨((279144375184483/562949953421312), (-16574509109403/2251799813685248)), (22337/1125899906842624), by norm_num⟩
  | 1 => ⟨((1111853133647867/1125899906842624), (-12379430245957/562949953421312)), (67505/1125899906842624), by norm_num⟩
  | 0 => ⟨((1097556158111967/1125899906842624), (-49105998228051/1125899906842624)), (4281/35184372088832), by norm_num⟩
  | _ => zero

def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((1097556158111967/1125899906842624), (-49105998228051/1125899906842624)), (16330719128358353/134217728000000000000000000), by norm_num⟩
  | 1 => ⟨((1067784190975665/1125899906842624), (-95739577608769/1125899906842624)), (279037/1125899906842624), by norm_num⟩
  | 2 => ⟨((502263569302763/562949953421312), (-181595551789349/1125899906842624)), (144181/281474976710656), by norm_num⟩
  | 3 => ⟨((433474513068667/562949953421312), (-162019429004131/562949953421312)), (1215145/1125899906842624), by norm_num⟩
  | 4 => ⟨((1148591324133671/2251799813685248), (-998046702637071/2251799813685248)), (2570785/1125899906842624), by norm_num⟩
  | 5 => ⟨((143514004782479/2251799813685248), (-127270170372413/281474976710656)), (4901453/1125899906842624), by norm_num⟩
  | 6 => ⟨((-902439271306549/4503599627370496), (-129780999028337/2251799813685248)), (5057197/1125899906842624), by norm_num⟩
  | _ => zero

def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-420850299/268435456), (-2914012561/134217728)), (1/134217728), by norm_num⟩, -3, term6ValuePoly, term6ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term6Value_checks : CertifiedScalarExp.Checks term6Value := by
  constructor
  · norm_num [term6Value, CertifiedScalarExp.reduced, term6ValuePoly, term6ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term6Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term6ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term6Value, term6ValueSquares, term6ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term6Value, CertifiedScalarExp.roundingCheck, term6ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term6 : Sound J_term6 F_term6 c := by
  apply exp_sound (A_arg6 hcre) S_arg6 term6Value term6Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term6Value,J_arg6]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term6,J_arg6,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1945910149055313/1000000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log7 : Sound J_log7 F_log7 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log7_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-8357620451/4294967296), 0), (1/4294967296), by norm_num⟩
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
theorem S_negLog7 : Sound J_negLog7 F_negLog7 c := by
  apply sound_round (sound_scale (A_log7 hcre) S_log7)
  intro k
  fin_cases k <;> norm_num [J_negLog7, J_log7, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-57132171/33554432), (-6329428379/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-8357620451/4294967296), 0), (1/4294967296), by norm_num⟩
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
theorem S_arg7 : Sound J_arg7 F_arg7 c := by
  apply sound_round (sound_mul (A_negLog7 hcre) (A_variable hcre) S_negLog7 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg7, J_negLog7, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((13959340254257/4503599627370496), (1640839602999989/9007199254740992)), (8159017/2251799813685248), by norm_num⟩
  | 1 => ⟨((-51810497/8589934592), (-6090023873/17179869184)), (123/17179869184), by norm_num⟩
  | 2 => ⟨((25204643/4294967296), (5925319631/17179869184)), (121/17179869184), by norm_num⟩
  | 3 => ⟨((-130789255/34359738368), (-7686759737/34359738368)), (159/34359738368), by norm_num⟩
  | 4 => ⟨((127252069/68719476736), (7478871893/68719476736)), (157/68719476736), by norm_num⟩
  | 5 => ⟨((-99048437/137438953472), (-181915159/4294967296)), (31/34359738368), by norm_num⟩
  | 6 => ⟨((64246453/274877906944), (7551798489/549755813888)), (163/549755813888), by norm_num⟩
  | 7 => ⟨((-71438757/1099511627776), (-8397212185/2199023255552)), (183/2199023255552), by norm_num⟩
  | 8 => ⟨((69506701/4398046511104), (8170110207/8796093022208)), (45/2199023255552), by norm_num⟩
  | 9 => ⟨((-120225595/35184372088832), (-1766477819/8796093022208)), (79/17592186044416), by norm_num⟩
  | 10 => ⟨((46789641/70368744177664), (2749925693/70368744177664)), (125/140737488355328), by norm_num⟩
  | 11 => ⟨((-132434091/1125899906842624), (-1945857569/281474976710656)), (179/1125899906842624), by norm_num⟩
  | 12 => ⟨((42950807/2251799813685248), (157769333/140737488355328)), (117/4503599627370496), by norm_num⟩
  | _ => zero

def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581757847530181/10141204801825835211973625643008), (63249248757/316912650057057350374175801344)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((222417446908021/79228162514264337593543950336), (599185164979/158456325028528675187087900672)), (2889/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1890383773783019/39614081257132168796771975168), (168495293465/2475880078570760549798248448)), (13001/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890198679402451/2475880078570760549798248448), (2863921947597/2475880078570760549798248448)), (1727/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((885932302562579/77371252455336267181195264), (2863361751667/154742504910672534362390528)), (13819/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775092439680577/4835703278458516698824704), (670951636603/2417851639229258349412352)), (6479/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629670431057805/302231454903657293676544), (1173867879367/302231454903657293676544)), (11341/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888688690820229/75557863725914323419136), (3813955308943/75557863725914323419136)), (18433/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649105686978939/2361183241434822606848), (714872715909/1180591620717411303424)), (13829/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405592772388809/147573952589676412928), (982553765405/147573952589676412928)), (9511/295147905179352825856), by norm_num⟩
  | 8 => ⟨((912313481677805/36893488147419103232), (4910392394201/73786976294838206464)), (23787/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911975690398027/4611686018427387904), (5520925279759/9223372036854775808)), (3347/1152921504606846976), by norm_num⟩
  | 6 => ⟨((797598753937511/576460752303423488), (5516844721889/1152921504606846976)), (13397/576460752303423488), by norm_num⟩
  | 5 => ⟨((298909570314121/36028797018963968), (75353928989/2251799813685248)), (23465/144115188075855872), by norm_num⟩
  | 4 => ⟨((373304585709991/9007199254740992), (3612404603317/18014398509481984)), (35237/36028797018963968), by norm_num⟩
  | 3 => ⟨((372806135040189/2251799813685248), (9014984141931/9007199254740992)), (22059/4503599627370496), by norm_num⟩
  | 2 => ⟨((2231853933420241/4503599627370496), (17981952529797/4503599627370496)), (88449/4503599627370496), by norm_num⟩
  | 1 => ⟨((2221893142841173/2251799813685248), (26853121509919/2251799813685248)), (133209/2251799813685248), by norm_num⟩
  | 0 => ⟨((2192036098257219/2251799813685248), (13307101405271/562949953421312)), (268567/2251799813685248), by norm_num⟩
  | _ => zero

def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((2192036098257219/2251799813685248), (13307101405271/562949953421312)), (1024501809127043967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1066300157703319/1125899906842624), (103631402636223/2251799813685248)), (66947/281474976710656), by norm_num⟩
  | 2 => ⟨((1007470693017463/1125899906842624), (98145652470923/1125899906842624)), (1063747/2251799813685248), by norm_num⟩
  | 3 => ⟨((446471583344163/562949953421312), (351288308705235/2251799813685248)), (2089167/2251799813685248), by norm_num⟩
  | 4 => ⟨((1361571531037117/2251799813685248), (557208492317043/2251799813685248)), (1982821/1125899906842624), by norm_num⟩
  | 5 => ⟨((342702695159797/1125899906842624), (336921255335465/1125899906842624)), (6758323/2251799813685248), by norm_num⟩
  | 6 => ⟨((13959340254257/4503599627370496), (1640839602999989/9007199254740992)), (8159017/2251799813685248), by norm_num⟩
  | _ => zero

def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-57132171/33554432), (-6329428379/268435456)), (1/134217728), by norm_num⟩, -4, term7ValuePoly, term7ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term7Value_checks : CertifiedScalarExp.Checks term7Value := by
  constructor
  · norm_num [term7Value, CertifiedScalarExp.reduced, term7ValuePoly, term7ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term7Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term7ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term7Value, term7ValueSquares, term7ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term7Value, CertifiedScalarExp.roundingCheck, term7ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term7 : Sound J_term7 F_term7 c := by
  apply exp_sound (A_arg7 hcre) S_arg7 term7Value term7Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term7Value,J_arg7]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term7,J_arg7,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((519860385419959/250000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log8 : Sound J_log8 F_log8 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log8_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1116391677/536870912), 0), (1/2147483648), by norm_num⟩
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
theorem S_negLog8 : Sound J_negLog8 F_negLog8 c := by
  apply sound_round (sound_scale (A_log8 hcre) S_log8)
  intro k
  fin_cases k <;> norm_num [J_negLog8, J_log8, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-488421359/268435456), (-6763763637/268435456)), (3/268435456), by norm_num⟩
  | 1 => ⟨((-1116391677/536870912), 0), (1/2147483648), by norm_num⟩
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
theorem S_arg8 : Sound J_arg8 F_arg8 c := by
  apply sound_round (sound_mul (A_negLog8 hcre) (A_variable hcre) S_negLog8 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg8, J_negLog8, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((364274904651979/2251799813685248), (-93735729959265/9007199254740992)), (17880881/9007199254740992), by norm_num⟩
  | 1 => ⟨((-5779177623/17179869184), (371776525/17179869184)), (73/17179869184), by norm_num⟩
  | 2 => ⟨((6008731013/17179869184), (-386543775/17179869184)), (39/8589934592), by norm_num⟩
  | 3 => ⟨((-4164934961/17179869184), (16745733/1073741824)), (7/2147483648), by norm_num⟩
  | 4 => ⟨((1082592347/8589934592), (-278574183/34359738368)), (15/8589934592), by norm_num⟩
  | 5 => ⟨((-7203799997/137438953472), (463422983/137438953472)), (103/137438953472), by norm_num⟩
  | 6 => ⟨((2496646829/137438953472), (-160610167/137438953472)), (37/137438953472), by norm_num⟩
  | 7 => ⟨((-2966646361/549755813888), (95422701/274877906944)), (45/549755813888), by norm_num⟩
  | 8 => ⟨((6168967683/4398046511104), (-396851857/4398046511104)), (3/137438953472), by norm_num⟩
  | 9 => ⟨((-2850668371/8796093022208), (183384497/8796093022208)), (91/17592186044416), by norm_num⟩
  | 10 => ⟨((2371119293/35184372088832), (-305069873/70368744177664)), (77/70368744177664), by norm_num⟩
  | 11 => ⟨((-896473447/70368744177664), (115340903/140737488355328)), (119/562949953421312), by norm_num⟩
  | 12 => ⟨((2485552169/1125899906842624), (-319792887/2251799813685248)), (21/562949953421312), by norm_num⟩
  | _ => zero

def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581605650422191/10141204801825835211973625643008), (-20920538821/2535301200456458802993406410752)), (7279/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779162430563429/633825300114114700748351602688), (-49537587677/316912650057057350374175801344)), (8645/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890184693687381/39614081257132168796771975168), (-111441778059/39614081257132168796771975168)), (19451/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((922845420491/1208925819614629174706176), (-29596228719/618970019642690137449562112)), (20667/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771653644124543/154742504910672534362390528), (-231172269/302231454903657293676544)), (5167/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((193748427385423/1208925819614629174706176), (-110936438703/9671406556917033397649408)), (1211/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((1259168399860469/604462909807314587353088), (-97043141665/604462909807314587353088)), (16955/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888409030829267/75557863725914323419136), (-157645918535/75557863725914323419136)), (27551/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298002145875591/4722366482869645213696), (-118191418013/4722366482869645213696)), (2583/590295810358705651712), by norm_num⟩
  | 9 => ⟨((811042120118245/295147905179352825856), (-81221661761/295147905179352825856)), (7103/147573952589676412928), by norm_num⟩
  | 8 => ⟨((28504213428895/1152921504606846976), (-101474698613/36893488147419103232)), (8879/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1823551141349093/9223372036854775808), (-228174123641/9223372036854775808)), (9989/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1594799424818575/1152921504606846976), (-227994327561/1152921504606846976)), (39957/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195292380511833/144115188075855872), (-199292957285/144115188075855872)), (8741/36028797018963968), by norm_num⟩
  | 4 => ⟨((1492704325570845/36028797018963968), (-298535754919/36028797018963968)), (52449/36028797018963968), by norm_num⟩
  | 3 => ⟨((1490590455315877/9007199254740992), (-186232162627/4503599627370496)), (65565/9007199254740992), by norm_num⟩
  | 2 => ⟨((557652746038885/1125899906842624), (-742816832033/4503599627370496)), (16393/562949953421312), by norm_num⟩
  | 1 => ⟨((1110045728234957/1125899906842624), (-277240168737/562949953421312)), (98377/1125899906842624), by norm_num⟩
  | 0 => ⟨((547170450119399/562949953421312), (-274619081667/281474976710656)), (393665/2251799813685248), by norm_num⟩
  | _ => zero

def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((547170450119399/562949953421312), (-274619081667/281474976710656)), (1501712807662200217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((531832710886181/562949953421312), (-4270744015205/2251799813685248)), (766031/2251799813685248), by norm_num⟩
  | 2 => ⟨((1004866918262129/1125899906842624), (-4034677244937/1125899906842624)), (362571/562949953421312), by norm_num⟩
  | 3 => ⟨((1793660766219953/2251799813685248), (-3600953925533/562949953421312)), (2599155/2251799813685248), by norm_num⟩
  | 4 => ⟨((178580010466443/281474976710656), (-22946586061303/2251799813685248)), (2086971/1125899906842624), by norm_num⟩
  | 5 => ⟨((906157790151509/2251799813685248), (-29116631445423/2251799813685248)), (2690665/1125899906842624), by norm_num⟩
  | 6 => ⟨((364274904651979/2251799813685248), (-93735729959265/9007199254740992)), (17880881/9007199254740992), by norm_num⟩
  | _ => zero

def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-488421359/268435456), (-6763763637/268435456)), (3/268435456), by norm_num⟩, -4, term8ValuePoly, term8ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term8Value_checks : CertifiedScalarExp.Checks term8Value := by
  constructor
  · norm_num [term8Value, CertifiedScalarExp.reduced, term8ValuePoly, term8ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term8Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term8ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term8Value, term8ValueSquares, term8ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term8Value, CertifiedScalarExp.roundingCheck, term8ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term8 : Sound J_term8 F_term8 c := by
  apply exp_sound (A_arg8 hcre) S_arg8 term8Value term8Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term8Value,J_arg8]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term8,J_arg8,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term2Jet : Jet 12 := J_term2
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨30,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 12 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨30,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 12 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨30,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 12 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨30,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 12 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨30,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 12 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨30,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 12 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨30,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiRectangle.Tile030Terms0
