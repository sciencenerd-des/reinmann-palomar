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
namespace Reinmann.XiRectangle.Tile043Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨43,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((7/8), (17907/1280)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((7/8), (17907/1280))
  have he : value ((7/8), (17907/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-10175445/4194304), (-650756047/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((737850343302293/18014398509481984), (-705492387900647/9007199254740992)), (214056593/18014398509481984), by norm_num⟩
  | 1 => ⟨((-487746129/4294967296), (932712669/4294967296)), (9/268435456), by norm_num⟩
  | 2 => ⟨((169039927/1073741824), (-646507157/2147483648)), (101/2147483648), by norm_num⟩
  | 3 => ⟨((-156226065/1073741824), (149374871/536870912)), (189/4294967296), by norm_num⟩
  | 4 => ⟨((216575313/2147483648), (-828310165/4294967296)), (133/4294967296), by norm_num⟩
  | 5 => ⟨((-60047427/1073741824), (918625369/8589934592)), (149/8589934592), by norm_num⟩
  | 6 => ⟨((221982425/8589934592), (-848990113/17179869184)), (35/4294967296), by norm_num⟩
  | 7 => ⟨((-351694839/34359738368), (672542975/34359738368)), (7/2147483648), by norm_num⟩
  | 8 => ⟨((121888143/34359738368), (-466171267/68719476736)), (157/137438953472), by norm_num⟩
  | 9 => ⟨((-600792339/549755813888), (1148889953/549755813888)), (49/137438953472), by norm_num⟩
  | 10 => ⟨((666300025/2199023255552), (-1274159731/2199023255552)), (55/549755813888), by norm_num⟩
  | 11 => ⟨((-671773067/8796093022208), (642312891/4398046511104)), (7/274877906944), by norm_num⟩
  | 12 => ⟨((620850143/35184372088832), (-1187246319/35184372088832)), (209/35184372088832), by norm_num⟩
  | _ => zero

def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395203902880331/2535301200456458802993406410752), (-1418506538131/10141204801825835211973625643008)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778226031628655/633825300114114700748351602688), (-419438797289/158456325028528675187087900672)), (92365/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472282839022783/9903520314283042199192993792), (-943538393285/19807040628566084398385987584)), (51961/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888868381539095/2475880078570760549798248448), (-2004522962347/2475880078570760549798248448)), (110429/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221316844067043/19342813113834066795298816), (-2003965054235/154742504910672534362390528)), (110443/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774469307756813/4835703278458516698824704), (-1878124666167/9671406556917033397649408)), (25889/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((629125427017567/302231454903657293676544), (-1642766741601/604462909807314587353088)), (45313/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943459156902855/37778931862957161709568), (-2668385805591/75557863725914323419136)), (73647/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((162110545773889/590295810358705651712), (-2000318463555/4722366482869645213696)), (110495/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620547712571105/590295810358705651712), (-2748861108697/590295810358705651712)), (75985/295147905179352825856), by norm_num⟩
  | 8 => ⟨((911174814497831/36893488147419103232), (-1716856412193/36893488147419103232)), (190021/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910695986091555/4611686018427387904), (-3859679639177/9223372036854775808)), (213855/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796320668542103/576460752303423488), (-3855624438777/1152921504606846976)), (53489/288230376151711744), by norm_num⟩
  | 5 => ⟨((596702635220325/72057594037927936), (-3369114654339/144115188075855872)), (93663/72057594037927936), by norm_num⟩
  | 4 => ⟨((744938047033081/18014398509481984), (-5044571933631/36028797018963968)), (281219/36028797018963968), by norm_num⟩
  | 3 => ⟨((743529712597619/4503599627370496), (-6289819965177/9007199254740992)), (175963/4503599627370496), by norm_num⟩
  | 2 => ⟨((2223561703449383/4503599627370496), (-12532075385179/4503599627370496)), (176265/1125899906842624), by norm_num⟩
  | 1 => ⟨((1104774745033719/1125899906842624), (-18679621825061/2251799813685248)), (1060625/2251799813685248), by norm_num⟩
  | 0 => ⟨((1083862859325811/1125899906842624), (-9221947876661/562949953421312)), (533363/562949953421312), by norm_num⟩
  | _ => zero

def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((1083862859325811/1125899906842624), (-9221947876661/562949953421312)), (2034618379833030523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((521546592817829/562949953421312), (-35510534225663/1125899906842624)), (1044373/562949953421312), by norm_num⟩
  | 2 => ⟨((1930513341858659/2251799813685248), (-131595343578791/2251799813685248)), (4002007/1125899906842624), by norm_num⟩
  | 3 => ⟨((1647377536003821/2251799813685248), (-225638677968947/2251799813685248)), (3664879/562949953421312), by norm_num⟩
  | 4 => ⟨((1182582890783855/2251799813685248), (-82536664023279/562949953421312)), (12193585/1125899906842624), by norm_num⟩
  | 5 => ⟨((143163867321631/562949953421312), (-693535516918367/4503599627370496)), (16382981/1125899906842624), by norm_num⟩
  | 6 => ⟨((737850343302293/18014398509481984), (-705492387900647/9007199254740992)), (214056593/18014398509481984), by norm_num⟩
  | _ => zero

def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-10175445/4194304), (-650756047/16777216)), (1/16777216), by norm_num⟩, -6, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-41591753/16777216), (-332492645/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-540832073554603/18014398509481984), (-1409822987744623/18014398509481984)), (16633511/1125899906842624), by norm_num⟩
  | 1 => ⟨((91331759/1073741824), (952322317/4294967296)), (91/2147483648), by norm_num⟩
  | 2 => ⟨((-517524717/4294967296), (-337266537/1073741824)), (65/1073741824), by norm_num⟩
  | 3 => ⟨((488752645/4294967296), (1274064071/4294967296)), (31/536870912), by norm_num⟩
  | 4 => ⟨((-346185129/4294967296), (-112802979/536870912)), (177/4294967296), by norm_num⟩
  | 5 => ⟨((392326531/8589934592), (1022703697/8589934592)), (101/4294967296), by norm_num⟩
  | 6 => ⟨((-370514921/17179869184), (-965845921/17179869184)), (193/17179869184), by norm_num⟩
  | 7 => ⟨((74981987/8589934592), (390921079/17179869184)), (79/17179869184), by norm_num⟩
  | 8 => ⟨((-106219983/34359738368), (-553781409/68719476736)), (113/68719476736), by norm_num⟩
  | 9 => ⟨((267505665/274877906944), (1394649669/549755813888)), (287/549755813888), by norm_num⟩
  | 10 => ⟨((-37895031/137438953472), (-790268011/1099511627776)), (41/274877906944), by norm_num⟩
  | 11 => ⟨((312333695/4398046511104), (814181045/4398046511104)), (171/4398046511104), by norm_num⟩
  | 12 => ⟨((-294969331/17592186044416), (-1537832401/35184372088832)), (325/35184372088832), by norm_num⟩
  | _ => zero

def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580746512500455/10141204801825835211973625643008), (-630822305357/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444535260684369/158456325028528675187087900672), (-746047098171/158456325028528675187087900672)), (92495/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889035582982895/39614081257132168796771975168), (-419560460257/4951760157141521099596496896)), (104075/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888766407615087/2475880078570760549798248448), (-445670187719/309485009821345068724781056)), (55301/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((442608134252775/38685626227668133590597632), (-1782173309157/77371252455336267181195264)), (55313/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774421265983001/4835703278458516698824704), (-1670248483801/4835703278458516698824704)), (51869/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314541631168265/151115727451828646838272), (-91308038339/18889465931478580854784)), (90797/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886780798607393/75557863725914323419136), (-4745998236737/75557863725914323419136)), (73797/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296780810303789/4722366482869645213696), (-444716521287/590295810358705651712)), (110739/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202550580311311/73786976294838206464), (-1222253155485/147573952589676412928)), (9521/36893488147419103232), by norm_num⟩
  | 8 => ⟨((911084885961705/36893488147419103232), (-1526741166701/18446744073709551616)), (47631/18446744073709551616), by norm_num⟩
  | 7 => ⟨((455297058463067/2305843009213693952), (-6864425377567/9223372036854775808)), (53621/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1592435853815485/1152921504606846976), (-3428522132775/576460752303423488)), (26833/144115188075855872), by norm_num⟩
  | 5 => ⟨((1193223514972593/144115188075855872), (-5991618540851/144115188075855872)), (188035/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489599559240547/36028797018963968), (-4485429406061/18014398509481984)), (282459/36028797018963968), by norm_num⟩
  | 3 => ⟨((185838369916791/1125899906842624), (-1398078229905/1125899906842624)), (353787/9007199254740992), by norm_num⟩
  | 2 => ⟨((1111418250719201/2251799813685248), (-22282600735705/4503599627370496)), (709717/4503599627370496), by norm_num⟩
  | 1 => ⟨((2208411435690277/2251799813685248), (-33207945118703/2251799813685248)), (8359/17592186044416), by norm_num⟩
  | 0 => ⟨((1082625569013753/1125899906842624), (-32778043560769/1125899906842624)), (2161501/2251799813685248), by norm_num⟩
  | _ => zero

def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((1082625569013753/1125899906842624), (-32778043560769/1125899906842624)), (8245471962935637717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((520030117875461/562949953421312), (-63036417083735/1125899906842624)), (2141351/1125899906842624), by norm_num⟩
  | 2 => ⟨((957235805386877/1125899906842624), (-232921844702371/2251799813685248)), (8391927/2251799813685248), by norm_num⟩
  | 3 => ⟨((1603583471662827/2251799813685248), (-396058527495795/2251799813685248)), (16005659/2251799813685248), by norm_num⟩
  | 4 => ⟨((1072305619137767/2251799813685248), (-564093579405677/2251799813685248)), (14213337/1125899906842624), by norm_num⟩
  | 5 => ⟨((738642724325197/4503599627370496), (-537241997481391/2251799813685248)), (10328935/562949953421312), by norm_num⟩
  | 6 => ⟨((-540832073554603/18014398509481984), (-1409822987744623/18014398509481984)), (16633511/1125899906842624), by norm_num⟩
  | _ => zero

def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-41591753/16777216), (-332492645/8388608)), (1/16777216), by norm_num⟩, -6, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-84861685/33554432), (-1356801955/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-330055655668759/4503599627370496), (-282876274916819/9007199254740992)), (256827389/18014398509481984), by norm_num⟩
  | 1 => ⟨((454894803/2147483648), (389870451/4294967296)), (89/2147483648), by norm_num⟩
  | 2 => ⟨((-328703773/1073741824), (-563435271/4294967296)), (65/1073741824), by norm_num⟩
  | 3 => ⟨((1266768137/4294967296), (271422899/2147483648)), (253/4294967296), by norm_num⟩
  | 4 => ⟨((-57209857/268435456), (-392256541/4294967296)), (23/536870912), by norm_num⟩
  | 5 => ⟨((33071551/268435456), (453506891/8589934592)), (215/8589934592), by norm_num⟩
  | 6 => ⟨((-509808411/8589934592), (-436934503/17179869184)), (209/17179869184), by norm_num⟩
  | 7 => ⟨((210505119/8589934592), (360829471/34359738368)), (87/17179869184), by norm_num⟩
  | 8 => ⟨((-608438051/68719476736), (-65183207/17179869184)), (253/137438953472), by norm_num⟩
  | 9 => ⟨((195401351/68719476736), (41867489/34359738368)), (41/68719476736), by norm_num⟩
  | 10 => ⟨((-451826037/549755813888), (-387240345/1099511627776)), (191/1099511627776), by norm_num⟩
  | 11 => ⟨((237444585/1099511627776), (101751687/1099511627776)), (101/2199023255552), by norm_num⟩
  | 12 => ⟨((-457535415/8796093022208), (-392133603/17592186044416)), (197/17592186044416), by norm_num⟩
  | _ => zero

def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395170341040317/2535301200456458802993406410752), (-3564906068827/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889029621731719/316912650057057350374175801344), (-2107858373027/316912650057057350374175801344)), (11577/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1888943316330013/39614081257132168796771975168), (-4741620537203/39614081257132168796771975168)), (104219/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944334024654333/1237940039285380274899124224), (-1259167473899/618970019642690137449562112)), (27691/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((110645863342707/9671406556917033397649408), (-5035205505357/154742504910672534362390528)), (110799/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774374795465201/4835703278458516698824704), (-2359474808537/4835703278458516698824704)), (103911/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157260601737233/75557863725914323419136), (-4127525786847/604462909807314587353088)), (90959/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943323646521857/37778931862957161709568), (-6704314422797/75557863725914323419136)), (73939/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648340023516889/2361183241434822606848), (-5025686093351/4722366482869645213696)), (110969/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620265064014801/590295810358705651712), (-431636045997/36893488147419103232)), (152681/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455498439464413/18446744073709551616), (-8626511359591/73786976294838206464)), (190999/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910494051624135/4611686018427387904), (-4848145926453/4611686018427387904)), (107539/4611686018427387904), by norm_num⟩
  | 6 => ⟨((796116542906285/576460752303423488), (-9685632149715/1152921504606846976)), (215333/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596521567119893/72057594037927936), (-4231472851501/72057594037927936)), (188703/144115188075855872), by norm_num⟩
  | 4 => ⟨((372330772876563/9007199254740992), (-12670478052513/36028797018963968)), (141815/18014398509481984), by norm_num⟩
  | 3 => ⟨((1486351102320543/9007199254740992), (-7898128253789/4503599627370496)), (355545/9007199254740992), by norm_num⟩
  | 2 => ⟨((555523539244139/1125899906842624), (-15733604620345/2251799813685248)), (89265/562949953421312), by norm_num⟩
  | 1 => ⟨((1103610996981225/1125899906842624), (-11722080711767/562949953421312)), (539389/1125899906842624), by norm_num⟩
  | 0 => ⟨((540643111064387/562949953421312), (-23132824069177/562949953421312)), (1094033/1125899906842624), by norm_num⟩
  | _ => zero

def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((540643111064387/562949953421312), (-23132824069177/562949953421312)), (4173404697898482921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2073078391560753/2251799813685248), (-177729503611559/2251799813685248)), (2191277/1125899906842624), by norm_num⟩
  | 2 => ⟨((947256993089531/1125899906842624), (-327246846047961/2251799813685248)), (273789/70368744177664), by norm_num⟩
  | 3 => ⟨((773179908004571/1125899906842624), (-550647284898929/2251799813685248)), (17288747/2251799813685248), by norm_num⟩
  | 4 => ⟨((14488523215903/35184372088832), (-756282888902719/2251799813685248)), (32200577/2251799813685248), by norm_num⟩
  | 5 => ⟨((255668795594011/4503599627370496), (-155714334847193/562949953421312)), (48149245/2251799813685248), by norm_num⟩
  | 6 => ⟨((-330055655668759/4503599627370496), (-282876274916819/9007199254740992)), (256827389/18014398509481984), by norm_num⟩
  | _ => zero

def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-84861685/33554432), (-1356801955/33554432)), (1/16777216), by norm_num⟩, -6, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-86449105/33554432), (-691091129/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-1286186973552811/18014398509481984), (471736075532779/18014398509481984)), (243098819/18014398509481984), by norm_num⟩
  | 1 => ⟨((902914777/4294967296), (-331162951/4294967296)), (173/4294967296), by norm_num⟩
  | 2 => ⟨((-332322183/1073741824), (487544551/4294967296)), (257/4294967296), by norm_num⟩
  | 3 => ⟨((326167463/1073741824), (-119628765/1073741824)), (127/2147483648), by norm_num⟩
  | 4 => ⟨((-30011881/134217728), (352239599/4294967296)), (189/4294967296), by norm_num⟩
  | 5 => ⟨((1131112349/8589934592), (-207429601/4294967296)), (7/268435456), by norm_num⟩
  | 6 => ⟨((-1110163763/17179869184), (101793967/4294967296)), (111/8589934592), by norm_num⟩
  | 7 => ⟨((933945559/34359738368), (-171272071/17179869184)), (47/8589934592), by norm_num⟩
  | 8 => ⟨((-687486427/68719476736), (252150081/68719476736)), (279/137438953472), by norm_num⟩
  | 9 => ⟨((449835963/137438953472), (-5155837/4294967296)), (23/34359738368), by norm_num⟩
  | 10 => ⟨((-1059611635/1099511627776), (194317407/549755813888)), (109/549755813888), by norm_num⟩
  | 11 => ⟨((283632891/1099511627776), (-416113271/4398046511104)), (235/4398046511104), by norm_num⟩
  | 12 => ⟨((-1113519653/17592186044416), (51050839/2199023255552)), (233/17592186044416), by norm_num⟩
  | _ => zero

def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395154934790955/2535301200456458802993406410752), (908589829883/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888992998085851/316912650057057350374175801344), (4297513595157/633825300114114700748351602688)), (5789/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((1888860911902349/39614081257132168796771975168), (604200228381/4951760157141521099596496896)), (104229/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236072561242943/309485009821345068724781056), (5134349916371/2475880078570760549798248448)), (110775/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885123124457677/77371252455336267181195264), (320801823659/9671406556917033397649408)), (55405/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387166873411827/2417851639229258349412352), (1202602990631/2417851639229258349412352)), (51961/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629006486652671/302231454903657293676544), (2103747757339/302231454903657293676544)), (45485/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((235816317736299/9444732965739290427392), (6834153110135/75557863725914323419136)), (18487/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1296592474817479/4722366482869645213696), (5122967053959/4722366482869645213696)), (13873/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1620144637956411/590295810358705651712), (1759944703047/147573952589676412928)), (1193/4611686018427387904), by norm_num⟩
  | 8 => ⟨((455460801026773/18446744073709551616), (4396637626797/36893488147419103232)), (191031/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455204675376687/2305843009213693952), (9883573288593/9223372036854775808)), (215117/9223372036854775808), by norm_num⟩
  | 6 => ⟨((99503978039089/72057594037927936), (4936252029021/576460752303423488)), (107689/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192894837537501/144115188075855872), (4312999230115/72057594037927936)), (188749/144115188075855872), by norm_num⟩
  | 4 => ⟨((744550284951499/18014398509481984), (12914138253317/36028797018963968)), (70927/9007199254740992), by norm_num⟩
  | 3 => ⟨((1486072820339985/9007199254740992), (16099226752033/9007199254740992)), (355663/9007199254740992), by norm_num⟩
  | 2 => ⟨((1110768609481783/2251799813685248), (16034173619669/2251799813685248)), (357209/2251799813685248), by norm_num⟩
  | 1 => ⟨((1103192853545901/1125899906842624), (23889033758953/1125899906842624)), (539685/1125899906842624), by norm_num⟩
  | 0 => ⟨((1080448340221877/1125899906842624), (47131600029057/1125899906842624)), (1094931/1125899906842624), by norm_num⟩
  | _ => zero

def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((1080448340221877/1125899906842624), (47131600029057/1125899906842624)), (4176830296043014171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1034858623831267/1125899906842624), (11307234931345/140737488355328)), (1096565/562949953421312), by norm_num⟩
  | 2 => ⟨((1887822775194109/2251799813685248), (10392921705805/70368744177664)), (8767975/2251799813685248), by norm_num⟩
  | 3 => ⟨((1533559813023101/2251799813685248), (278816888468155/1125899906842624)), (17291395/2251799813685248), by norm_num⟩
  | 4 => ⟨((906319584243673/2251799813685248), (759538876854483/2251799813685248)), (16058113/1125899906842624), by norm_num⟩
  | 5 => ⟨((108586865423923/2251799813685248), (1222817330215629/4503599627370496)), (95037023/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1286186973552811/18014398509481984), (471736075532779/18014398509481984)), (243098819/18014398509481984), by norm_num⟩
  | _ => zero

def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-86449105/33554432), (-691091129/16777216)), (1/16777216), by norm_num⟩, -7, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-87955083/33554432), (-1406260421/33554432)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-314947482494187/9007199254740992), (1148440376806919/18014398509481984)), (58974393/9007199254740992), by norm_num⟩
  | 1 => ⟨((224947533/2147483648), (-102532503/536870912)), (43/2147483648), by norm_num⟩
  | 2 => ⟨((-673882585/4294967296), (1228639713/4294967296)), (131/4294967296), by norm_num⟩
  | 3 => ⟨((21028873/134217728), (-153361485/536870912)), (133/4294967296), by norm_num⟩
  | 4 => ⟨((-125993747/1073741824), (229714975/1073741824)), (51/2147483648), by norm_num⟩
  | 5 => ⟨((603909655/8589934592), (-1101063303/8589934592)), (31/2147483648), by norm_num⟩
  | 6 => ⟨((-150762637/4294967296), (1099496957/17179869184)), (63/8589934592), by norm_num⟩
  | 7 => ⟨((129041285/8589934592), (-941085291/34359738368)), (55/17179869184), by norm_num⟩
  | 8 => ⟨((-193286571/34359738368), (704809895/68719476736)), (21/17179869184), by norm_num⟩
  | 9 => ⟨((514697617/274877906944), (-469204833/137438953472)), (57/137438953472), by norm_num⟩
  | 10 => ⟨((-616758505/1099511627776), (1124489649/1099511627776)), (69/549755813888), by norm_num⟩
  | 11 => ⟨((83983789/549755813888), (-1224970885/4398046511104)), (19/549755813888), by norm_num⟩
  | 12 => ⟨((-335457263/8796093022208), (76451767/1099511627776)), (77/8796093022208), by norm_num⟩
  | _ => zero

def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790280637907115/5070602400912917605986812821504), (2699624508691/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((888960653169747/316912650057057350374175801344), (797995736353/158456325028528675187087900672)), (23129/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888788397889141/39614081257132168796771975168), (224384937675/2475880078570760549798248448)), (26025/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944251895567175/1237940039285380274899124224), (476690416863/309485009821345068724781056)), (55315/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770169940480381/154742504910672534362390528), (1906187772707/77371252455336267181195264)), (1729/4835703278458516698824704), by norm_num⟩
  | 13 => ⟨((774298184475097/4835703278458516698824704), (893220733935/2417851639229258349412352)), (12971/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1257951153305251/604462909807314587353088), (1562526933633/302231454903657293676544)), (45413/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886430860101237/75557863725914323419136), (2537964198241/37778931862957161709568)), (36911/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324129597869535/1180591620717411303424), (3804948603995/4722366482869645213696)), (27695/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620043873723765/590295810358705651712), (5228559816763/590295810358705651712)), (76197/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910859448457531/36893488147419103232), (6377769571/72057594037927936)), (95303/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910340559045333/4611686018427387904), (7340507855131/9223372036854775808)), (107293/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795964443496471/576460752303423488), (3666080947861/576460752303423488)), (53695/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192780087464977/144115188075855872), (6406262628745/144115188075855872)), (94075/144115188075855872), by norm_num⟩
  | 4 => ⟨((744467378579821/18014398509481984), (9590661300693/36028797018963968)), (141329/36028797018963968), by norm_num⟩
  | 3 => ⟨((371469138838551/2251799813685248), (11955601641133/9007199254740992)), (44261/2251799813685248), by norm_num⟩
  | 2 => ⟨((2221177509453951/4503599627370496), (23813256635429/4503599627370496)), (177617/2251799813685248), by norm_num⟩
  | 1 => ⟨((551481889391225/562949953421312), (17737908141377/1125899906842624)), (267865/1125899906842624), by norm_num⟩
  | 0 => ⟨((540075559200951/562949953421312), (8747517065131/281474976710656)), (541513/1125899906842624), by norm_num⟩
  | _ => zero

def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((540075559200951/562949953421312), (8747517065131/281474976710656)), (2065708164695357921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2070347686547797/2251799813685248), (134273255144151/2251799813685248)), (2145355/2251799813685248), by norm_num⟩
  | 2 => ⟨((1895510520165371/2251799813685248), (61726695566685/562949953421312)), (2100407/1125899906842624), by norm_num⟩
  | 3 => ⟨((1568521833718375/2251799813685248), (415680293108155/2251799813685248)), (7993515/2251799813685248), by norm_num⟩
  | 4 => ⟨((126980128454955/281474976710656), (289547770465235/1125899906842624)), (1760897/281474976710656), by norm_num⟩
  | 5 => ⟨((4833504068591/35184372088832), (1044975678255507/4503599627370496)), (39911457/4503599627370496), by norm_num⟩
  | 6 => ⟨((-314947482494187/9007199254740992), (1148440376806919/18014398509481984)), (58974393/9007199254740992), by norm_num⟩
  | _ => zero

def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-87955083/33554432), (-1406260421/33554432)), (1/33554432), by norm_num⟩, -7, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-5586723/2097152), (-1429163561/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((225801612572211/18014398509481984), (1234619960155079/18014398509481984)), (23999325/2251799813685248), by norm_num⟩
  | 1 => ⟨((-327805555/8589934592), (-1792348943/8589934592)), (281/8589934592), by norm_num⟩
  | 2 => ⟨((124751421/2147483648), (341052911/1073741824)), (27/536870912), by norm_num⟩
  | 3 => ⟨((-253205667/4294967296), (-692228827/2147483648)), (221/4294967296), by norm_num⟩
  | 4 => ⟨((24090323/536870912), (526876549/2147483648)), (85/2147483648), by norm_num⟩
  | 5 => ⟨((-234699293/8589934592), (-320817495/2147483648)), (209/8589934592), by norm_num⟩
  | 6 => ⟨((238182421/17179869184), (1302314749/17179869184)), (107/8589934592), by norm_num⟩
  | 7 => ⟨((-207186207/34359738368), (-141604517/4294967296)), (47/8589934592), by norm_num⟩
  | 8 => ⟨((39423941/17179869184), (1724472517/137438953472)), (9/4294967296), by norm_num⟩
  | 9 => ⟨((-213381463/274877906944), (-291677515/68719476736)), (197/274877906944), by norm_num⟩
  | 10 => ⟨((259857861/1099511627776), (1420829983/1099511627776)), (121/549755813888), by norm_num⟩
  | 11 => ⟨((-71922099/1099511627776), (-1572999551/4398046511104)), (135/2199023255552), by norm_num⟩
  | 12 => ⟨((145978963/8796093022208), (1596344143/17592186044416)), (69/4398046511104), by norm_num⟩
  | _ => zero

def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790252832762771/5070602400912917605986812821504), (905252546125/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888929281229455/316912650057057350374175801344), (535138666093/158456325028528675187087900672)), (92411/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472179498241593/9903520314283042199192993792), (2407568663565/39614081257132168796771975168)), (103977/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472107306861485/618970019642690137449562112), (1278673319911/1237940039285380274899124224)), (110491/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770095648245159/154742504910672534362390528), (2556565039777/154742504910672534362390528)), (27627/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((774263504089815/4835703278458516698824704), (1197974791249/4835703278458516698824704)), (103621/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257890750584413/604462909807314587353088), (65488315271/18889465931478580854784)), (90687/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886333245068945/75557863725914323419136), (850959315521/18889465931478580854784)), (147401/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296445651646179/4722366482869645213696), (79734935663/147573952589676412928)), (55291/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1619944621568363/590295810358705651712), (3506128538139/590295810358705651712)), (38025/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1821595977677569/73786976294838206464), (4379350135493/73786976294838206464)), (23775/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1820544406857613/9223372036854775808), (1230555206541/2305843009213693952)), (107039/4611686018427387904), by norm_num⟩
  | 6 => ⟨((397948534432405/288230376151711744), (2458270797175/576460752303423488)), (214209/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596332191677587/72057594037927936), (4295592813459/144115188075855872)), (187579/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488765589711779/36028797018963968), (803830896007/4503599627370496)), (281661/36028797018963968), by norm_num⟩
  | 3 => ⟨((742836372127143/4503599627370496), (8016055551661/9007199254740992)), (352589/9007199254740992), by norm_num⟩
  | 2 => ⟨((277599088008603/562949953421312), (15965531274409/4503599627370496)), (706721/4503599627370496), by norm_num⟩
  | 1 => ⟨((1102703472901405/1125899906842624), (11891238610681/1125899906842624)), (1063955/2251799813685248), by norm_num⟩
  | 0 => ⟨((2159484737234941/2251799813685248), (46905442955931/2251799813685248)), (8373/8796093022208), by norm_num⟩
  | _ => zero

def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((2159484737234941/2251799813685248), (46905442955931/2251799813685248)), (31940460238632557/33554432000000000000000000), by norm_num⟩
  | 1 => ⟨((2069977171791035/2251799813685248), (89965002697825/2251799813685248)), (2100263/1125899906842624), by norm_num⟩
  | 2 => ⟨((118702597474307/140737488355328), (82700735968107/1125899906842624)), (8058349/2251799813685248), by norm_num⟩
  | 3 => ⟨((1589733169438581/2251799813685248), (279010014664071/2251799813685248)), (14777171/2251799813685248), by norm_num⟩
  | 4 => ⟨((135969289257209/281474976710656), (393952848047457/2251799813685248)), (24526815/2251799813685248), by norm_num⟩
  | 5 => ⟨((913056831267743/4503599627370496), (761211378373133/4503599627370496)), (8069447/562949953421312), by norm_num⟩
  | 6 => ⟨((225801612572211/18014398509481984), (1234619960155079/18014398509481984)), (23999325/2251799813685248), by norm_num⟩
  | _ => zero

def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-5586723/2097152), (-1429163561/33554432)), (1/16777216), by norm_num⟩, -7, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨43,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 12 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨43,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 12 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨43,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 12 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨43,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 12 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨43,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 12 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨43,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiRectangle.Tile043Terms2
