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
namespace Reinmann.XiRectangle.Tile035Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨35,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5/8), (8601/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((5/8), (8601/640))
  have he : value ((5/8), (8601/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-372130559/536870912), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-7268175/16777216), (-312567865/33554432)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-372130559/536870912), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-362840496840421/562949953421312), (-79802988067747/1125899906842624)), (14815465/562949953421312), by norm_num⟩
  | 1 => ⟨((479701743/1073741824), (52752701/1073741824)), (81/4294967296), by norm_num⟩
  | 2 => ⟨((-1330015643/8589934592), (-18282693/1073741824)), (29/4294967296), by norm_num⟩
  | 3 => ⟨((1229195457/34359738368), (135174369/34359738368)), (7/4294967296), by norm_num⟩
  | 4 => ⟨((-1704026731/274877906944), (-93695733/137438953472)), (5/17179869184), by norm_num⟩
  | 5 => ⟨((1889826119/2199023255552), (103911893/1099511627776)), (91/2199023255552), by norm_num⟩
  | 6 => ⟨((-1746570195/17592186044416), (-96034981/8796093022208)), (43/8796093022208), by norm_num⟩
  | 7 => ⟨((1383577379/140737488355328), (152151717/140737488355328)), (35/70368744177664), by norm_num⟩
  | 8 => ⟨((-1918045519/2251799813685248), (-210927067/2251799813685248)), (99/2251799813685248), by norm_num⟩
  | 9 => ⟨((295441743/4503599627370496), (32489667/4503599627370496)), (63/18014398509481984), by norm_num⟩
  | 10 => ⟨((-163827689/36028797018963968), (-144128775/288230376151711744)), (9/36028797018963968), by norm_num⟩
  | 11 => ⟨((1321387063/4611686018427387904), (36328165/1152921504606846976)), (75/4611686018427387904), by norm_num⟩
  | 12 => ⟨((-305305239/18446744073709551616), (-67148707/36893488147419103232)), (71/73786976294838206464), by norm_num⟩
  | _ => zero

def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583411453608229/10141204801825835211973625643008), (-3949600554683/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((890645579846413/316912650057057350374175801344), (-4686808795287/633825300114114700748351602688)), (11583/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((946289278635141/19807040628566084398385987584), (-329526157549/2475880078570760549798248448)), (26069/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((946264870824173/1237940039285380274899124224), (-5601692643381/2475880078570760549798248448)), (13853/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1774194660187721/154742504910672534362390528), (-2800704398261/77371252455336267181195264)), (6929/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((776184117952333/4835703278458516698824704), (-656377357377/1208925819614629174706176)), (12997/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1261250229074943/604462909807314587353088), (-4594339276245/604462909807314587353088)), (22755/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((118236837873725/4722366482869645213696), (-7465233933935/75557863725914323419136)), (9249/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1300535155077937/4722366482869645213696), (-5598428267111/4722366482869645213696)), (6941/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1625563436562295/590295810358705651712), (-962128700029/73786976294838206464)), (19101/295147905179352825856), by norm_num⟩
  | 8 => ⟨((914306559749913/36893488147419103232), (-4810035374243/36893488147419103232)), (23897/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1828429925448791/9223372036854775808), (-5410451713439/4611686018427387904)), (841/144115188075855872), by norm_num⟩
  | 6 => ⟨((1599668702338425/1152921504606846976), (-10818802495205/1152921504606846976)), (53895/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1199542308934567/144115188075855872), (-4732040384101/72057594037927936)), (47237/144115188075855872), by norm_num⟩
  | 4 => ⟨((1499057853148839/36028797018963968), (-14191358670287/36028797018963968)), (35507/18014398509481984), by norm_num⟩
  | 3 => ⟨((187311875868933/1125899906842624), (-17730819820779/9007199254740992)), (89045/9007199254740992), by norm_num⟩
  | 2 => ⟨((280788517279725/562949953421312), (-4429540951467/562949953421312)), (44731/1125899906842624), by norm_num⟩
  | 1 => ⟨((1121678875495063/1125899906842624), (-13272648660275/562949953421312)), (67619/562949953421312), by norm_num⟩
  | 0 => ⟨((1117049635620115/1125899906842624), (-26480477444231/562949953421312)), (274665/1125899906842624), by norm_num⟩
  | _ => zero

def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((1117049635620115/1125899906842624), (-26480477444231/562949953421312)), (1047763828757857921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1105777714457487/1125899906842624), (-26272324476051/281474976710656)), (570853/1125899906842624), by norm_num⟩
  | 2 => ⟨((1076206318068551/1125899906842624), (-51605565887437/281474976710656)), (1227867/1125899906842624), by norm_num⟩
  | 3 => ⟨((495430313734631/562949953421312), (-394622901862097/1125899906842624)), (2797581/1125899906842624), by norm_num⟩
  | 4 => ⟨((366852125741487/562949953421312), (-694584471988013/1125899906842624)), (1721291/281474976710656), by norm_num⟩
  | 5 => ⟨((49626382929557/1125899906842624), (-1810532453247269/2251799813685248)), (34937395/2251799813685248), by norm_num⟩
  | 6 => ⟨((-362840496840421/562949953421312), (-79802988067747/1125899906842624)), (14815465/562949953421312), by norm_num⟩
  | _ => zero

def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-7268175/16777216), (-312567865/33554432)), (1/67108864), by norm_num⟩, -1, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-1179625963/1073741824), 0), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((-46079139/67108864), (-495408345/33554432)), (3/134217728), by norm_num⟩
  | 1 => ⟨((-1179625963/1073741824), 0), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((-665042939425167/2251799813685248), (-917601645128609/2251799813685248)), (37566205/1125899906842624), by norm_num⟩
  | 1 => ⟨((348388837/1073741824), (961388057/2147483648)), (81/2147483648), by norm_num⟩
  | 2 => ⟨((-765488515/4294967296), (-528096367/2147483648)), (91/4294967296), by norm_num⟩
  | 3 => ⟨((140162515/2147483648), (773564211/8589934592)), (69/8589934592), by norm_num⟩
  | 4 => ⟨((-307968523/17179869184), (-212461787/8589934592)), (39/17179869184), by norm_num⟩
  | 5 => ⟨((270670403/68719476736), (23341313/4294967296)), (71/137438953472), by norm_num⟩
  | 6 => ⟨((-792964883/1099511627776), (-136762951/137438953472)), (107/1099511627776), by norm_num⟩
  | 7 => ⟨((248903133/2199023255552), (171713667/1099511627776)), (69/4398046511104), by norm_num⟩
  | 8 => ⟨((-546896081/35184372088832), (-754586979/35184372088832)), (39/17592186044416), by norm_num⟩
  | 9 => ⟨((534068227/281474976710656), (736887581/281474976710656)), (39/140737488355328), by norm_num⟩
  | 10 => ⟨((-234693567/1125899906842624), (-323821501/1125899906842624)), (71/2251799813685248), by norm_num⟩
  | 11 => ⟨((375035981/18014398509481984), (1034921543/36028797018963968)), (29/9007199254740992), by norm_num⟩
  | 12 => ⟨((-274679425/144115188075855872), (-757985017/288230376151711744)), (87/288230376151711744), by norm_num⟩
  | _ => zero

def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197885168922433/1267650600228229401496703205376), (-2863073449679/10141204801825835211973625643008)), (7279/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1780905073661599/633825300114114700748351602688), (-3396060112529/633825300114114700748351602688)), (34701/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((473036144275291/9903520314283042199192993792), (-3820318322257/39614081257132168796771975168)), (19523/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((946034537976425/1237940039285380274899124224), (-2029401056125/1237940039285380274899124224)), (5187/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1773734487557227/154742504910672534362390528), (-2029240070575/77371252455336267181195264)), (20753/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1551937347917401/9671406556917033397649408), (-3804482952233/9671406556917033397649408)), (9731/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((630436862954355/302231454903657293676544), (-416072538329/75557863725914323419136)), (17035/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((236397321304415/9444732965739290427392), (-5408301024807/75557863725914323419136)), (27691/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((325019471922775/1180591620717411303424), (-4055663837043/4722366482869645213696)), (10389/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1624936090095347/590295810358705651712), (-5575624253459/590295810358705651712)), (3573/36893488147419103232), by norm_num⟩
  | 8 => ⟨((1827831030479231/73786976294838206464), (-3484079681095/36893488147419103232)), (4469/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1827552954274467/9223372036854775808), (-7837293130591/9223372036854775808)), (10063/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1598795329332829/1152921504606846976), (-979366726077/144115188075855872)), (20145/288230376151711744), by norm_num⟩
  | 5 => ⟨((1198782154733333/144115188075855872), (-107076728187/2251799813685248)), (35297/72057594037927936), by norm_num⟩
  | 4 => ⟨((1497925714280849/36028797018963968), (-10274047353937/36028797018963968)), (53031/18014398509481984), by norm_num⟩
  | 3 => ⟨((1497093990741427/9007199254740992), (-12833239161307/9007199254740992)), (132879/9007199254740992), by norm_num⟩
  | 2 => ⟨((560887140030769/1125899906842624), (-12819234042907/2251799813685248)), (133333/2251799813685248), by norm_num⟩
  | 1 => ⟨((1119662227972233/1125899906842624), (-9596875390171/562949953421312)), (50283/281474976710656), by norm_num⟩
  | 0 => ⟨((139153536106213/140737488355328), (-9561644400233/281474976710656)), (406807/1125899906842624), by norm_num⟩
  | _ => zero

def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((139153536106213/140737488355328), (-9561644400233/281474976710656)), (1551845554832076671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((68712503597915/70368744177664), (-37816125463979/562949953421312)), (26003/35184372088832), by norm_num⟩
  | 2 => ⟨((1068443333093951/1125899906842624), (-147704250650967/1125899906842624)), (108551/70368744177664), by norm_num⟩
  | 3 => ⟨((994541880292619/1125899906842624), (-280333306572913/1125899906842624)), (3752065/1125899906842624), by norm_num⟩
  | 4 => ⟨((404355122221867/562949953421312), (-123813498932389/281474976710656)), (2124263/281474976710656), by norm_num⟩
  | 5 => ⟨((363030262901767/1125899906842624), (-177865269156723/281474976710656)), (39363543/2251799813685248), by norm_num⟩
  | 6 => ⟨((-665042939425167/2251799813685248), (-917601645128609/2251799813685248)), (37566205/1125899906842624), by norm_num⟩
  | _ => zero

def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-46079139/67108864), (-495408345/33554432)), (3/134217728), by norm_num⟩, -2, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-372130559/268435456), 0), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((-7268175/8388608), (-312567865/16777216)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-372130559/268435456), 0), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((924139676223943/2251799813685248), (102871509852239/1125899906842624)), (4384093/281474976710656), by norm_num⟩
  | 1 => ⟨((-1221780417/2147483648), (-272007359/2147483648)), (49/2147483648), by norm_num⟩
  | 2 => ⟨((1693747303/4294967296), (94270567/1073741824)), (35/2147483648), by norm_num⟩
  | 3 => ⟨((-782677445/4294967296), (-348498015/8589934592)), (67/8589934592), by norm_num⟩
  | 4 => ⟨((1085021329/17179869184), (241560417/17179869184)), (49/17179869184), by norm_num⟩
  | 5 => ⟨((-150415895/8589934592), (-267899075/68719476736)), (7/8589934592), by norm_num⟩
  | 6 => ⟨((556055219/137438953472), (123795659/137438953472)), (53/274877906944), by norm_num⟩
  | 7 => ⟨((-880978531/1099511627776), (-98066985/549755813888)), (11/274877906944), by norm_num⟩
  | 8 => ⟨((610647785/4398046511104), (271899417/8796093022208)), (63/8796093022208), by norm_num⟩
  | 9 => ⟨((-376238925/17592186044416), (-335051225/70368744177664)), (5/4398046511104), by norm_num⟩
  | 10 => ⟨((1669049281/562949953421312), (371583699/562949953421312)), (91/562949953421312), by norm_num⟩
  | 11 => ⟨((-1682758987/4503599627370496), (-187317959/2251799813685248)), (47/2251799813685248), by norm_num⟩
  | 12 => ⟨((777599765/18014398509481984), (346237107/36028797018963968)), (89/36028797018963968), by norm_num⟩
  | _ => zero

def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582847140111075/10141204801825835211973625643008), (35668659315/1267650600228229401496703205376)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780633387356123/633825300114114700748351602688), (21148086255/39614081257132168796771975168)), (46117/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472959829966967/9903520314283042199192993792), (380635972189/39614081257132168796771975168)), (51883/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472936304122879/618970019642690137449562112), (404389955777/2475880078570760549798248448)), (55127/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886705581950479/77371252455336267181195264), (101087431453/38685626227668133590597632)), (6891/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((387908700291295/2417851639229258349412352), (47379391145/1208925819614629174706176)), (12921/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((630304783272043/302231454903657293676544), (331613005469/604462909807314587353088)), (45225/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1890750378144041/75557863725914323419136), (538791023625/75557863725914323419136)), (73493/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299757676533843/4722366482869645213696), (101005796125/1180591620717411303424)), (55123/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((812248657726267/295147905179352825856), (277709009157/295147905179352825856)), (75797/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1827284834802589/73786976294838206464), (694101775821/73786976294838206464)), (2961/2305843009213693952), by norm_num⟩
  | 7 => ⟨((1826941607503623/9223372036854775808), (390314895613/4611686018427387904)), (26651/2305843009213693952), by norm_num⟩
  | 6 => ⟨((799093942261617/576460752303423488), (780336513951/1152921504606846976)), (53307/576460752303423488), by norm_num⟩
  | 5 => ⟨((1198255027142825/144115188075855872), (341232329191/72057594037927936)), (93299/144115188075855872), by norm_num⟩
  | 4 => ⟨((1497143788406595/36028797018963968), (255759442195/9007199254740992)), (139971/36028797018963968), by norm_num⟩
  | 3 => ⟨((748065952827999/4503599627370496), (4990798423/35184372088832)), (43751/2251799813685248), by norm_num⟩
  | 2 => ⟨((560417571783197/1125899906842624), (79744800593/140737488355328)), (21883/281474976710656), by norm_num⟩
  | 1 => ⟨((2236621545658175/2251799813685248), (1909561965243/1125899906842624)), (262747/1125899906842624), by norm_num⟩
  | 0 => ⟨((2221507289964783/2251799813685248), (475238150039/140737488355328)), (131525/281474976710656), by norm_num⟩
  | _ => zero

def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((2221507289964783/2251799813685248), (475238150039/140737488355328)), (501728058935069949/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((2191596602611619/2251799813685248), (1875379877669/281474976710656)), (2083197/2251799813685248), by norm_num⟩
  | 2 => ⟨((1066451499864599/1125899906842624), (29203847649523/2251799813685248)), (4082763/2251799813685248), by norm_num⟩
  | 3 => ⟨((63122040116163/70368744177664), (1728866334963/70368744177664)), (980035/281474976710656), by norm_num⟩
  | 4 => ⟨((1810532453247253/2251799813685248), (24813191464777/562949953421312)), (7225499/1125899906842624), by norm_num⟩
  | 5 => ⟨((725680993680829/1125899906842624), (159605976135483/2251799813685248)), (12256109/1125899906842624), by norm_num⟩
  | 6 => ⟨((924139676223943/2251799813685248), (102871509852239/1125899906842624)), (4384093/281474976710656), by norm_num⟩
  | _ => zero

def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-7268175/8388608), (-312567865/16777216)), (1/33554432), by norm_num⟩, -3, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-54003775/33554432), 0), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((-67504719/67108864), (-1451520215/67108864)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-54003775/33554432), 0), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((-770201742585199/2251799813685248), (-583000890697263/4503599627370496)), (142801287/4503599627370496), by norm_num⟩
  | 1 => ⟨((1182166943/2147483648), (447418087/2147483648)), (7/134217728), by norm_num⟩
  | 2 => ⟨((-951312149/2147483648), (-45005727/268435456)), (23/536870912), by norm_num⟩
  | 3 => ⟨((31897455/134217728), (193157129/2147483648)), (101/4294967296), by norm_num⟩
  | 4 => ⟨((-410695787/4294967296), (-310874407/8589934592)), (83/8589934592), by norm_num⟩
  | 5 => ⟨((66098937/2147483648), (400266445/34359738368)), (109/34359738368), by norm_num⟩
  | 6 => ⟨((-1134742775/137438953472), (-26841833/8589934592)), (119/137438953472), by norm_num⟩
  | 7 => ⟨((521799441/274877906944), (394973839/549755813888)), (111/549755813888), by norm_num⟩
  | 8 => ⟨((-839803803/2199023255552), (-39730367/274877906944)), (91/2199023255552), by norm_num⟩
  | 9 => ⟨((9386195/137438953472), (56838719/2199023255552)), (33/4398046511104), by norm_num⟩
  | 10 => ⟨((-386726351/35184372088832), (-585461691/140737488355328)), (43/35184372088832), by norm_num⟩
  | 11 => ⟨((226331655/140737488355328), (342641543/562949953421312)), (103/562949953421312), by norm_num⟩
  | 12 => ⟨((-485688995/2251799813685248), (-367640193/4503599627370496)), (7/281474976710656), by norm_num⟩
  | _ => zero

def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582665471740547/10141204801825835211973625643008), (-1810487413939/5070602400912917605986812821504)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780408219775331/633825300114114700748351602688), (-4292793674767/633825300114114700748351602688)), (5789/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1891585444921281/39614081257132168796771975168), (-2414466030905/19807040628566084398385987584)), (26057/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1891474777564509/2475880078570760549798248448), (-5130210394369/2475880078570760549798248448)), (55387/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886569970642055/77371252455336267181195264), (-5129614020859/154742504910672534362390528)), (13851/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((193922462194387/1208925819614629174706176), (-4808379349565/9671406556917033397649408)), (6495/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((630192759387435/302231454903657293676544), (-4206697969319/604462909807314587353088)), (11371/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1890384740941977/75557863725914323419136), (-6834695168611/75557863725914323419136)), (36973/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1299482084632301/4722366482869645213696), (-5124980620597/4722366482869645213696)), (55491/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((406029040317305/147573952589676412928), (-7045156463423/590295810358705651712)), (76349/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1826805071162931/73786976294838206464), (-4401953294051/36893488147419103232)), (11939/9223372036854775808), by norm_num⟩
  | 7 => ⟨((456599327629313/2305843009213693952), (-4950450961273/4611686018427387904)), (53777/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1597637888963301/1152921504606846976), (-1237066609609/144115188075855872)), (107683/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1197767377065517/144115188075855872), (-4327273618051/72057594037927936)), (2949/4503599627370496), by norm_num⟩
  | 4 => ⟨((187049940337763/4503599627370496), (-1621496647383/4503599627370496)), (141843/36028797018963968), by norm_num⟩
  | 3 => ⟨((1495179229012759/9007199254740992), (-1012356967511/562949953421312)), (177813/9007199254740992), by norm_num⟩
  | 2 => ⟨((1119849028215645/2251799813685248), (-16171786031339/2251799813685248)), (89289/1125899906842624), by norm_num⟩
  | 1 => ⟨((1116748276368379/1125899906842624), (-24192715818007/1125899906842624)), (269783/1125899906842624), by norm_num⟩
  | 0 => ⟨((1107296999266079/1125899906842624), (-48124687054423/1125899906842624)), (547251/1125899906842624), by norm_num⟩
  | _ => zero

def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((1107296999266079/1125899906842624), (-48124687054423/1125899906842624)), (2087596897605514171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1086944453625073/1125899906842624), (-94659074473891/1125899906842624)), (561601/562949953421312), by norm_num⟩
  | 2 => ⟨((1041378454479207/1125899906842624), (-182767855933503/1125899906842624)), (2357545/1125899906842624), by norm_num⟩
  | 3 => ⟨((466766623703917/562949953421312), (-169047449230417/562949953421312)), (5126531/1125899906842624), by norm_num⟩
  | 4 => ⟨((672507528465771/1125899906842624), (-140164692515727/281474976710656)), (723759/70368744177664), by norm_num⟩
  | 5 => ⟨((245009558232367/2251799813685248), (-1339540900487411/2251799813685248)), (50733617/2251799813685248), by norm_num⟩
  | 6 => ⟨((-770201742585199/2251799813685248), (-583000890697263/4503599627370496)), (142801287/4503599627370496), by norm_num⟩
  | _ => zero

def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-67504719/67108864), (-1451520215/67108864)), (1/33554432), by norm_num⟩, -3, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-1923887081/1073741824), 0), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((-75151839/67108864), (-403988105/16777216)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-1923887081/1073741824), 0), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((363603962925407/2251799813685248), (79820426646067/281474976710656)), (95125275/4503599627370496), by norm_num⟩
  | 1 => ⟨((-621310085/2147483648), (-1091148417/2147483648)), (83/2147483648), by norm_num⟩
  | 2 => ⟨((278309557/1073741824), (488768877/1073741824)), (19/536870912), by norm_num⟩
  | 3 => ⟨((-332442523/2147483648), (-583837509/2147483648)), (93/4294967296), by norm_num⟩
  | 4 => ⟨((595657039/8589934592), (1046096385/8589934592)), (85/8589934592), by norm_num⟩
  | 5 => ⟨((-53363707/2147483648), (-374870621/8589934592)), (63/17179869184), by norm_num⟩
  | 6 => ⟨((509946279/68719476736), (895570647/68719476736)), (77/68719476736), by norm_num⟩
  | 7 => ⟨((-130528725/68719476736), (-458470625/137438953472)), (81/274877906944), by norm_num⟩
  | 8 => ⟨((233876079/549755813888), (205367271/274877906944)), (37/549755813888), by norm_num⟩
  | 9 => ⟨((-93122151/1099511627776), (-654166671/4398046511104)), (15/1099511627776), by norm_num⟩
  | 10 => ⟨((533927987/35184372088832), (468843731/17592186044416)), (11/4398046511104), by norm_num⟩
  | 11 => ⟨((-695760383/281474976710656), (-1221898465/281474976710656)), (29/70368744177664), by norm_num⟩
  | 12 => ⟨((415545085/1125899906842624), (729782715/1125899906842624)), (71/1125899906842624), by norm_num⟩
  | _ => zero

def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582517037882311/10141204801825835211973625643008), (342969094881/2535301200456458802993406410752)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780240681350983/633825300114114700748351602688), (1626102623913/633825300114114700748351602688)), (46181/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472849371199781/9903520314283042199192993792), (1829181386855/39614081257132168796771975168)), (51959/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236409464312471/309485009821345068724781056), (1943282957523/2475880078570760549798248448)), (13803/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((886470801591725/77371252455336267181195264), (1943032936149/154742504910672534362390528)), (27609/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((96949657851815/604462909807314587353088), (455331940529/2417851639229258349412352)), (25887/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1260224263123211/604462909807314587353088), (398349053133/151115727451828646838272)), (22655/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1890124143300471/75557863725914323419136), (2588770961071/75557863725914323419136)), (73641/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299287898292581/4722366482869645213696), (485285662243/1180591620717411303424)), (27621/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1623851204590511/590295810358705651712), (667090870585/147573952589676412928)), (75977/590295810358705651712), by norm_num⟩
  | 8 => ⟨((913238473905145/36893488147419103232), (1667196557659/36893488147419103232)), (94999/73786976294838206464), by norm_num⟩
  | 7 => ⟨((57063512296319/288230376151711744), (1874866731563/4611686018427387904)), (106913/9223372036854775808), by norm_num⟩
  | 6 => ⟨((399319561170107/288230376151711744), (1873955294363/576460752303423488)), (53481/576460752303423488), by norm_num⟩
  | 5 => ⟨((1197458614086553/144115188075855872), (819342969283/36028797018963968)), (93647/144115188075855872), by norm_num⟩
  | 4 => ⟨((1495948214570785/36028797018963968), (613995019213/4503599627370496)), (35145/9007199254740992), by norm_num⟩
  | 3 => ⟨((373658943305651/2251799813685248), (1533196009885/2251799813685248)), (87959/4503599627370496), by norm_num⟩
  | 2 => ⟨((559668261507361/1125899906842624), (12244088641729/4503599627370496)), (88103/1125899906842624), by norm_num⟩
  | 1 => ⟨((2232113310422745/2251799813685248), (4578125231585/562949953421312)), (265033/1125899906842624), by norm_num⟩
  | 0 => ⟨((1106220863152721/1125899906842624), (36410872934921/2251799813685248)), (1065935/2251799813685248), by norm_num⟩
  | _ => zero

def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((1106220863152721/1125899906842624), (36410872934921/2251799813685248)), (4066219338423918967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2173182807321049/2251799813685248), (71548930844423/2251799813685248)), (2129081/2251799813685248), by norm_num⟩
  | 2 => ⟨((261879643777597/281474976710656), (17262736395163/281474976710656)), (4244797/2251799813685248), by norm_num⟩
  | 3 => ⟨((485179510841023/562949953421312), (256975412059537/2251799813685248)), (8419241/2251799813685248), by norm_num⟩
  | 4 => ⟨((205410697420071/281474976710656), (221474758037517/1125899906842624)), (16433887/2251799813685248), by norm_num⟩
  | 5 => ⟨((34752523380467/70368744177664), (646498456680829/2251799813685248)), (30451155/2251799813685248), by norm_num⟩
  | 6 => ⟨((363603962925407/2251799813685248), (79820426646067/281474976710656)), (95125275/4503599627370496), by norm_num⟩
  | _ => zero

def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-75151839/67108864), (-403988105/16777216)), (1/33554432), by norm_num⟩, -4, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-2089405113/1073741824), 0), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((-81617387/67108864), (-1754977869/67108864)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-2089405113/1073741824), 0), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((700262952359297/4503599627370496), (-568104863358383/2251799813685248)), (42525225/2251799813685248), by norm_num⟩
  | 1 => ⟨((-649761575/2147483648), (131783607/268435456)), (81/2147483648), by norm_num⟩
  | 2 => ⟨((316094411/1073741824), (-1025756233/2147483648)), (81/2147483648), by norm_num⟩
  | 3 => ⟨((-205030441/1073741824), (665343155/2147483648)), (27/1073741824), by norm_num⟩
  | 4 => ⟨((6233919/67108864), (-647348999/4294967296)), (107/8589934592), by norm_num⟩
  | 5 => ⟨((-9704517/268435456), (503873195/8589934592)), (85/17179869184), by norm_num⟩
  | 6 => ⟨((805722373/68719476736), (-1307322619/68719476736)), (7/4294967296), by norm_num⟩
  | 7 => ⟨((-447960955/137438953472), (726837815/137438953472)), (1/2147483648), by norm_num⟩
  | 8 => ⟨((108961471/137438953472), (-707180541/549755813888)), (1/8589934592), by norm_num⟩
  | 9 => ⟨((-753881715/4398046511104), (4778159/17179869184)), (7/274877906944), by norm_num⟩
  | 10 => ⟨((9168663/274877906944), (-952101693/17592186044416)), (89/17592186044416), by norm_num⟩
  | 11 => ⟨((-207608953/35184372088832), (42106917/4398046511104)), (1/1099511627776), by norm_num⟩
  | 12 => ⟨((269325579/281474976710656), (-218496739/140737488355328)), (85/562949953421312), by norm_num⟩
  | _ => zero

def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791195769420077/5070602400912917605986812821504), (-1326666835193/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((890046014500633/316912650057057350374175801344), (-786132765395/316912650057057350374175801344)), (23089/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1891230274098109/39614081257132168796771975168), (-1768606065483/39614081257132168796771975168)), (51955/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945549040557161/1237940039285380274899124224), (-1878910591431/2475880078570760549798248448)), (6901/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((886382000638813/77371252455336267181195264), (-939324052619/77371252455336267181195264)), (27607/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387757014321385/2417851639229258349412352), (-1760953746931/9671406556917033397649408)), (25885/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((315019659190371/151115727451828646838272), (-1540555721659/604462909807314587353088)), (22653/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((944943781575593/37778931862957161709568), (-2502880379991/75557863725914323419136)), (73635/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649555259011889/2361183241434822606848), (-1876703045983/4722366482869645213696)), (55237/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1623607395823605/590295810358705651712), (-2579723853373/590295810358705651712)), (37985/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1826172320475183/73786976294838206464), (-3223540876831/73786976294838206464)), (94989/73786976294838206464), by norm_num⟩
  | 7 => ⟨((912844935706475/4611686018427387904), (-1812476163327/4611686018427387904)), (26725/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1596935952140149/1152921504606846976), (-3623039138123/1152921504606846976)), (26737/288230376151711744), by norm_num⟩
  | 5 => ⟨((1197159366231509/144115188075855872), (-3168007955165/144115188075855872)), (93633/144115188075855872), by norm_num⟩
  | 4 => ⟨((1495499858767491/36028797018963968), (-2373855983333/18014398509481984)), (140555/36028797018963968), by norm_num⟩
  | 3 => ⟨((373519057713897/2251799813685248), (-5927120900159/9007199254740992)), (175879/9007199254740992), by norm_num⟩
  | 2 => ⟨((69923645817141/140737488355328), (-11831708145865/4503599627370496)), (176159/2251799813685248), by norm_num⟩
  | 1 => ⟨((2230445494647751/2251799813685248), (-4422827589679/562949953421312)), (264939/1125899906842624), by norm_num⟩
  | 0 => ⟨((2209133062362409/2251799813685248), (-17579053289729/1125899906842624)), (1065373/2251799813685248), by norm_num⟩
  | _ => zero

def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((2209133062362409/2251799813685248), (-17579053289729/1125899906842624)), (4064075478560637717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2166725818659493/2251799813685248), (-68983872529619/2251799813685248)), (1061821/1125899906842624), by norm_num⟩
  | 2 => ⟨((2082752636390447/2251799813685248), (-132755262499487/2251799813685248)), (527117/281474976710656), by norm_num⟩
  | 3 => ⟨((479642390768259/562949953421312), (-245578111593325/2251799813685248)), (8297945/2251799813685248), by norm_num⟩
  | 4 => ⟨((1607869641631739/2251799813685248), (-418472980943025/2251799813685248)), (7974945/1125899906842624), by norm_num⟩
  | 5 => ⟨((535155286463337/1125899906842624), (-149402712846009/562949953421312)), (7176469/562949953421312), by norm_num⟩
  | 6 => ⟨((700262952359297/4503599627370496), (-568104863358383/2251799813685248)), (42525225/2251799813685248), by norm_num⟩
  | _ => zero

def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-81617387/67108864), (-1754977869/67108864)), (1/33554432), by norm_num⟩, -4, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-1116391677/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-21804525/16777216), (-937703595/33554432)), (3/67108864), by norm_num⟩
  | 1 => ⟨((-1116391677/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-72632088210021/281474976710656), (-396221556074571/4503599627370496)), (39875685/1125899906842624), by norm_num⟩
  | 1 => ⟨((576149679/1073741824), (392875463/2147483648)), (161/2147483648), by norm_num⟩
  | 2 => ⟨((-1198069577/2147483648), (-408480779/2147483648)), (85/1073741824), by norm_num⟩
  | 3 => ⟨((830438549/2147483648), (70784325/536870912)), (15/268435456), by norm_num⟩
  | 4 => ⟨((-53964013/268435456), (-73595933/1073741824)), (127/4294967296), by norm_num⟩
  | 5 => ⟨((1436352133/17179869184), (489723009/17179869184)), (107/8589934592), by norm_num⟩
  | 6 => ⟨((-995603431/34359738368), (-339450123/34359738368)), (75/17179869184), by norm_num⟩
  | 7 => ⟨((295757019/34359738368), (403352393/137438953472)), (181/137438953472), by norm_num⟩
  | 8 => ⟨((-1230018863/549755813888), (-419373861/549755813888)), (95/274877906944), by norm_num⟩
  | 9 => ⟨((1136778809/2199023255552), (193791873/1099511627776)), (89/1099511627776), by norm_num⟩
  | 10 => ⟨((-59096627/549755813888), (-322383097/8796093022208)), (75/4398046511104), by norm_num⟩
  | 11 => ⟨((1429969235/70368744177664), (487546767/70368744177664)), (115/35184372088832), by norm_num⟩
  | 12 => ⟨((-123897393/35184372088832), (-337941667/281474976710656)), (81/140737488355328), by norm_num⟩
  | _ => zero

def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791141413306961/5070602400912917605986812821504), (-3664251280163/10141204801825835211973625643008)), (7279/1267650600228229401496703205376), by norm_num⟩
  | 17 => ⟨((889977226927461/316912650057057350374175801344), (-1085499282529/158456325028528675187087900672)), (34735/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1891075005230455/39614081257132168796771975168), (-305259718623/2475880078570760549798248448)), (78175/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890932482744605/2475880078570760549798248448), (-5188723755697/2475880078570760549798248448)), (83085/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886298849914449/77371252455336267181195264), (-1296986420199/38685626227668133590597632)), (83111/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775435701481641/4835703278458516698824704), (-303929517603/604462909807314587353088)), (77945/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629970408930467/302231454903657293676544), (-4254186351619/604462909807314587353088)), (68231/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889662208730861/75557863725914323419136), (-3455751089965/37778931862957161709568)), (6933/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((649470139537035/2361183241434822606848), (-323891850653/295147905179352825856)), (83243/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811685665525299/295147905179352825856), (-3561707575331/295147905179352825856)), (114535/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912937131295795/36893488147419103232), (-4450479948267/36893488147419103232)), (71641/36893488147419103232), by norm_num⟩
  | 7 => ⟨((28521101046029/144115188075855872), (-10009028823167/9223372036854775808)), (161349/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1596591441857265/1152921504606846976), (-5001669155825/576460752303423488)), (161545/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196852183760403/144115188075855872), (-8746516888735/144115188075855872)), (141573/144115188075855872), by norm_num⟩
  | 4 => ⟨((1495027633283371/36028797018963968), (-6553480661517/18014398509481984)), (212801/36028797018963968), by norm_num⟩
  | 3 => ⟨((11667702763771/70368744177664), (-8180632148159/4503599627370496)), (133387/4503599627370496), by norm_num⟩
  | 2 => ⟨((559069076923737/1125899906842624), (-4081895695035/562949953421312)), (133969/1125899906842624), by norm_num⟩
  | 1 => ⟨((278547010143499/281474976710656), (-6101770524405/281474976710656)), (202409/562949953421312), by norm_num⟩
  | 0 => ⟨((551100634869561/562949953421312), (-24238236691259/562949953421312)), (410657/562949953421312), by norm_num⟩
  | _ => zero

def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((551100634869561/562949953421312), (-24238236691259/562949953421312)), (1566532137157249273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((269228566228225/281474976710656), (-47456110609799/562949953421312)), (839389/562949953421312), by norm_num⟩
  | 2 => ⟨((1022058885734415/1125899906842624), (-90782781244373/562949953421312)), (3494515/1125899906842624), by norm_num⟩
  | 3 => ⟨((449257658819677/562949953421312), (-82409943973345/281474976710656)), (3735753/562949953421312), by norm_num⟩
  | 4 => ⟨((620541302060139/1125899906842624), (-526132715960525/1125899906842624)), (8150075/562949953421312), by norm_num⟩
  | 5 => ⟨((96150529989897/1125899906842624), (-289978779316319/562949953421312)), (33201813/1125899906842624), by norm_num⟩
  | 6 => ⟨((-72632088210021/281474976710656), (-396221556074571/4503599627370496)), (39875685/1125899906842624), by norm_num⟩
  | _ => zero

def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-21804525/16777216), (-937703595/33554432)), (3/67108864), by norm_num⟩, -4, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨35,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 12 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨35,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 12 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨35,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 12 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨35,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 12 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨35,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 12 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨35,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 12 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨35,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiRectangle.Tile035Terms0
