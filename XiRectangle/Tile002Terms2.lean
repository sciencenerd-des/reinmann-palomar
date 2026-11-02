/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 36 bits, checked against fixed final error disks.
module

public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile002Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨2,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (141/128)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (141/128))
  have he : value ((3/4), (141/128))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-47632711549/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-17862266831/8589934592), (-3279400551/1073741824)), (1/8589934592), by norm_num⟩
  | 1 => ⟨((-47632711549/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-1121601137096539/9007199254740992), (-49146437987773/4503599627370496)), (364301/9007199254740992), by norm_num⟩
  | 1 => ⟨((94901692613/274877906944), (8316824933/274877906944)), (33/274877906944), by norm_num⟩
  | 2 => ⟨((-65780840665/137438953472), (-2882391877/68719476736)), (25/137438953472), by norm_num⟩
  | 3 => ⟨((121588811311/274877906944), (2663895737/68719476736)), (49/274877906944), by norm_num⟩
  | 4 => ⟨((-21069735437/68719476736), (-3692943639/137438953472)), (9/68719476736), by norm_num⟩
  | 5 => ⟨((93468337365/549755813888), (2047802777/137438953472)), (21/274877906944), by norm_num⟩
  | 6 => ⟨((-86383086021/1099511627776), (-7570286513/1099511627776)), (41/1099511627776), by norm_num⟩
  | 7 => ⟨((8553741789/274877906944), (5996940289/2199023255552)), (35/2199023255552), by norm_num⟩
  | 8 => ⟨((-23716008017/2199023255552), (-8313524507/8796093022208)), (51/8796093022208), by norm_num⟩
  | 9 => ⟨((29224327273/8796093022208), (5122218731/17592186044416)), (65/35184372088832), by norm_num⟩
  | 10 => ⟨((-32410816085/35184372088832), (-5680722355/70368744177664)), (19/35184372088832), by norm_num⟩
  | 11 => ⟨((65354082295/281474976710656), (5727384267/281474976710656)), (5/35184372088832), by norm_num⟩
  | 12 => ⟨((-120799994349/2251799813685248), (-5293227009/1125899906842624)), (19/562949953421312), by norm_num⟩
  | _ => zero

def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581267062326477/10141204801825835211973625643008), (-994602536003/2535301200456458802993406410752)), (19/1267650600228229401496703205376), by norm_num⟩
  | 17 => ⟨((1778749785652087/633825300114114700748351602688), (-4708204094211/633825300114114700748351602688)), (91/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944859938007207/19807040628566084398385987584), (-661966695069/4951760157141521099596496896)), (205/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472373194043547/618970019642690137449562112), (-1406379891909/618970019642690137449562112)), (109/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771158126595605/154742504910672534362390528), (-5624172522265/154742504910672534362390528)), (217/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549521944960933/9671406556917033397649408), (-2635615318231/4835703278458516698824704)), (51/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258760184274985/604462909807314587353088), (-288180990769/37778931862957161709568)), (179/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887743946271905/75557863725914323419136), (-1872505759085/18889465931478580854784)), (145/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297501816514475/4722366482869645213696), (-701896276359/590295810358705651712)), (109/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621393826785291/590295810358705651712), (-3858522826181/295147905179352825856)), (299/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823402956711567/73786976294838206464), (-9640588028331/73786976294838206464)), (187/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1822571040655375/9223372036854775808), (-10837799557455/9223372036854775808)), (211/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1593813011019827/1152921504606846976), (-10827974650087/1152921504606846976)), (211/576460752303423488), by norm_num⟩
  | 5 => ⟨((298605545682513/36028797018963968), (-1182928541533/18014398509481984)), (185/72057594037927936), by norm_num⟩
  | 4 => ⟨((1491384898772985/36028797018963968), (-14173052400731/36028797018963968)), (139/9007199254740992), by norm_num⟩
  | 3 => ⟨((1488916536872203/9007199254740992), (-17677677909215/9007199254740992)), (697/9007199254740992), by norm_num⟩
  | 2 => ⟨((1113594806432345/2251799813685248), (-17619761952813/2251799813685248)), (175/562949953421312), by norm_num⟩
  | 1 => ⟨((553694214274773/562949953421312), (-13142497884901/562949953421312)), (529/562949953421312), by norm_num⟩
  | 0 => ⟨((1088665084916087/1125899906842624), (-25996134512715/562949953421312)), (537/281474976710656), by norm_num⟩
  | _ => zero

def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((1088665084916087/1125899906842624), (-25996134512715/562949953421312)), (2048493505382449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((262565185388683/281474976710656), (-100545648204697/1125899906842624)), (4353/1125899906842624), by norm_num⟩
  | 2 => ⟨((242681030355339/281474976710656), (-23447720885709/140737488355328)), (2225/281474976710656), by norm_num⟩
  | 3 => ⟨((100710373436983/140737488355328), (-161728538160681/562949953421312)), (18313/1125899906842624), by norm_num⟩
  | 4 => ⟨((241806839492885/562949953421312), (-231462727719809/562949953421312)), (73463/2251799813685248), by norm_num⟩
  | 5 => ⟨((34784998362933/2251799813685248), (-24855349178989/70368744177664)), (247041/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1121601137096539/9007199254740992), (-49146437987773/4503599627370496)), (364301/9007199254740992), by norm_num⟩
  | _ => zero

def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-17862266831/8589934592), (-3279400551/1073741824)), (1/8589934592), by norm_num⟩, 0, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-48674234621/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-18252837983/8589934592), (-53617711575/17179869184)), (1/8589934592), by norm_num⟩
  | 1 => ⟨((-48674234621/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-537812200396335/4503599627370496), (-2774305166417/1125899906842624)), (681981/18014398509481984), by norm_num⟩
  | 1 => ⟨((11625188467/34359738368), (959496877/137438953472)), (1/8589934592), by norm_num⟩
  | 2 => ⟨((-131746556367/274877906944), (-2718459355/274877906944)), (3/17179869184), by norm_num⟩
  | 3 => ⟨((31105508461/68719476736), (2567325107/274877906944)), (3/17179869184), by norm_num⟩
  | 4 => ⟨((-88128541645/274877906944), (-909222469/137438953472)), (9/68719476736), by norm_num⟩
  | 5 => ⟨((12484348009/68719476736), (2060816985/549755813888)), (43/549755813888), by norm_num⟩
  | 6 => ⟨((-47161095161/549755813888), (-1946244727/1099511627776)), (21/549755813888), by norm_num⟩
  | 7 => ⟨((76352825217/2199023255552), (1575464723/2199023255552)), (9/549755813888), by norm_num⟩
  | 8 => ⟨((-54080960815/4398046511104), (-1115906919/4398046511104)), (53/8796093022208), by norm_num⟩
  | 9 => ⟨((68099066595/17592186044416), (702578305/8796093022208)), (35/17592186044416), by norm_num⟩
  | 10 => ⟨((-77175673677/70368744177664), (-1592443383/70368744177664)), (21/35184372088832), by norm_num⟩
  | 11 => ⟨((39755481545/140737488355328), (1640629761/281474976710656)), (45/281474976710656), by norm_num⟩
  | 12 => ⟨((-9386313401/140737488355328), (-387354511/281474976710656)), (11/281474976710656), by norm_num⟩
  | _ => zero

def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581207834572467/10141204801825835211973625643008), (-2032700453857/5070602400912917605986812821504)), (153/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((111167448205133/39614081257132168796771975168), (-4810791290653/633825300114114700748351602688)), (91/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889640421357487/39614081257132168796771975168), (-5411100437543/39614081257132168796771975168)), (205/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889408335212399/2475880078570760549798248448), (-5748043987161/2475880078570760549798248448)), (217/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885536831371209/77371252455336267181195264), (-2873318718843/77371252455336267181195264)), (109/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((193680341976767/1208925819614629174706176), (-5385978280561/9671406556917033397649408)), (51/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258690852029453/604462909807314587353088), (-588904604605/75557863725914323419136)), (179/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943815618004473/37778931862957161709568), (-3826479325019/37778931862957161709568)), (145/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297417244213665/4722366482869645213696), (-2868634133609/2361183241434822606848)), (109/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621277475684245/590295810358705651712), (-985595260323/73786976294838206464)), (299/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823257421848569/73786976294838206464), (-4924990520557/36893488147419103232)), (375/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822407182430827/9223372036854775808), (-11073019590583/9223372036854775808)), (211/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1593648989131901/1152921504606846976), (-2765690243639/288230376151711744)), (211/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194278480440285/144115188075855872), (-2417094671149/36028797018963968)), (185/72057594037927936), by norm_num⟩
  | 4 => ⟨((1491168981517345/36028797018963968), (-7239751585655/18014398509481984)), (139/9007199254740992), by norm_num⟩
  | 3 => ⟨((93040375570497/562949953421312), (-18059036917671/9007199254740992)), (697/9007199254740992), by norm_num⟩
  | 2 => ⟨((556661671461307/1125899906842624), (-8999283523363/1125899906842624)), (701/2251799813685248), by norm_num⟩
  | 1 => ⟨((276744733058873/281474976710656), (-3355853552539/140737488355328)), (1059/1125899906842624), by norm_num⟩
  | 0 => ⟨((135979639660611/140737488355328), (-53090494010737/1125899906842624)), (1075/562949953421312), by norm_num⟩
  | _ => zero

def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((135979639660611/140737488355328), (-53090494010737/1125899906842624)), (4100801708030523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((65534854942117/70368744177664), (-102591375323639/1125899906842624)), (4359/1125899906842624), by norm_num⟩
  | 2 => ⟨((967180305670103/1125899906842624), (-191087988814245/1125899906842624)), (4457/562949953421312), by norm_num⟩
  | 3 => ⟨((798404119890109/1125899906842624), (-328300123852981/1125899906842624)), (18341/1125899906842624), by norm_num⟩
  | 4 => ⟨((940879671659219/2251799813685248), (-232805926931559/562949953421312)), (36709/1125899906842624), by norm_num⟩
  | 5 => ⟨((16055568172889/4503599627370496), (-389097401572665/1125899906842624)), (244155/4503599627370496), by norm_num⟩
  | 6 => ⟨((-537812200396335/4503599627370496), (-2774305166417/1125899906842624)), (681981/18014398509481984), by norm_num⟩
  | _ => zero

def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-18252837983/8589934592), (-53617711575/17179869184)), (1/8589934592), by norm_num⟩, 0, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-24828104347/8589934592), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-4655269565/2147483648), (-54699417389/17179869184)), (1/8589934592), by norm_num⟩
  | 1 => ⟨((-24828104347/8589934592), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-2059567994693919/18014398509481984), (87238751190915/18014398509481984)), (164591/4503599627370496), by norm_num⟩
  | 1 => ⟨((90834307333/274877906944), (-3847540629/274877906944)), (31/274877906944), by norm_num⟩
  | 2 => ⟨((-65636229141/137438953472), (2780205693/137438953472)), (47/274877906944), by norm_num⟩
  | 3 => ⟨((126475402003/274877906944), (-5357218677/274877906944)), (3/17179869184), by norm_num⟩
  | 4 => ⟨((-91390232505/274877906944), (3871088391/274877906944)), (9/68719476736), by norm_num⟩
  | 5 => ⟨((13207587349/68719476736), (-4475553823/549755813888)), (11/137438953472), by norm_num⟩
  | 6 => ⟨((-50899783285/549755813888), (2156002395/549755813888)), (45/1099511627776), by norm_num⟩
  | 7 => ⟨((84068169195/2199023255552), (-3560941961/2199023255552)), (39/2199023255552), by norm_num⟩
  | 8 => ⟨((-60747065495/4398046511104), (2573111519/4398046511104)), (29/4398046511104), by norm_num⟩
  | 9 => ⟨((39018133885/8796093022208), (-826360985/4398046511104)), (39/17592186044416), by norm_num⟩
  | 10 => ⟨((-45110764891/35184372088832), (3821584725/70368744177664)), (47/70368744177664), by norm_num⟩
  | 11 => ⟨((47413411207/140737488355328), (-4016654749/281474976710656)), (51/281474976710656), by norm_num⟩
  | 12 => ⟨((-91361589799/1125899906842624), (3869875149/1125899906842624)), (51/1125899906842624), by norm_num⟩
  | _ => zero

def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790575996580325/5070602400912917605986812821504), (2018566201271/5070602400912917605986812821504)), (19/1267650600228229401496703205376), by norm_num⟩
  | 17 => ⟨((1778613265412407/633825300114114700748351602688), (1194250434881/158456325028528675187087900672)), (91/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889566302346567/39614081257132168796771975168), (167908623167/1237940039285380274899124224)), (205/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889329613838429/2475880078570760549798248448), (2853813444705/1237940039285380274899124224)), (109/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((442748743802465/38685626227668133590597632), (1426550572029/38685626227668133590597632)), (109/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387342250551521/2417851639229258349412352), (2674025585595/4835703278458516698824704)), (51/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((314656592768261/151115727451828646838272), (584753935725/75557863725914323419136)), (179/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887526521855639/75557863725914323419136), (7598964141087/75557863725914323419136)), (145/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((20270918243247/73786976294838206464), (5696741104529/4722366482869645213696)), (109/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621169666108519/590295810358705651712), (1957246626735/147573952589676412928)), (75/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1823122803575371/73786976294838206464), (2445046416031/18446744073709551616)), (375/73786976294838206464), by norm_num⟩
  | 7 => ⟨((227781991802503/1152921504606846976), (2748598928959/2305843009213693952)), (421/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199187248499955/144115188075855872), (10984007450455/1152921504606846976)), (211/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194146632111967/144115188075855872), (9599324106883/144115188075855872)), (185/72057594037927936), by norm_num⟩
  | 4 => ⟨((745485882078677/18014398509481984), (14375632342781/36028797018963968)), (139/9007199254740992), by norm_num⟩
  | 3 => ⟨((744200229235159/4503599627370496), (17928696126679/9007199254740992)), (697/9007199254740992), by norm_num⟩
  | 2 => ⟨((69567452995795/140737488355328), (17867479713765/2251799813685248)), (175/562949953421312), by norm_num⟩
  | 1 => ⟨((553308212854731/562949953421312), (26648354941241/1125899906842624)), (1059/1125899906842624), by norm_num⟩
  | 0 => ⟨((135890828525735/140737488355328), (26343159919271/562949953421312)), (2149/1125899906842624), by norm_num⟩
  | _ => zero

def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((135890828525735/140737488355328), (26343159919271/562949953421312)), (8197788718795421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1047223159261673/1125899906842624), (50871929991781/562949953421312)), (17/4398046511104), by norm_num⟩
  | 2 => ⟨((964850006334967/1125899906842624), (23658525469253/140737488355328)), (8883/1125899906842624), by norm_num⟩
  | 3 => ⟨((1590040244842881/2251799813685248), (648780327562825/2251799813685248)), (4553/281474976710656), by norm_num⟩
  | 4 => ⟨((935834550647155/2251799813685248), (114529145155111/281474976710656)), (72429/2251799813685248), by norm_num⟩
  | 5 => ⟨((1007613448997/140737488355328), (1523124113479015/4503599627370496)), (14893/281474976710656), by norm_num⟩
  | 6 => ⟨((-2059567994693919/18014398509481984), (87238751190915/18014398509481984)), (164591/4503599627370496), by norm_num⟩
  | _ => zero

def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-4655269565/2147483648), (-54699417389/17179869184)), (1/8589934592), by norm_num⟩, -1, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-101170152965/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-18969403681/8589934592), (-55722623313/17179869184)), (1/8589934592), by norm_num⟩
  | 1 => ⟨((-101170152965/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-984614637802003/9007199254740992), (50335953003109/4503599627370496)), (644755/18014398509481984), by norm_num⟩
  | 1 => ⟨((88474661835/274877906944), (-9046090215/274877906944)), (31/274877906944), by norm_num⟩
  | 2 => ⟨((-8140882593/17179869184), (832364395/17179869184)), (25/137438953472), by norm_num⟩
  | 3 => ⟨((31960442709/68719476736), (-6535589785/137438953472)), (13/68719476736), by norm_num⟩
  | 4 => ⟨((-11763196663/34359738368), (9621822657/274877906944)), (5/34359738368), by norm_num⟩
  | 5 => ⟨((55417623639/274877906944), (-11332347873/549755813888)), (49/549755813888), by norm_num⟩
  | 6 => ⟨((-6798908799/68719476736), (5561234467/549755813888)), (25/549755813888), by norm_num⟩
  | 7 => ⟨((45757650477/1099511627776), (-9356980307/2199023255552)), (11/549755813888), by norm_num⟩
  | 8 => ⟨((-33682652415/2199023255552), (3443882193/2199023255552)), (17/2199023255552), by norm_num⟩
  | 9 => ⟨((88156901949/17592186044416), (-9013600861/17592186044416)), (23/8796093022208), by norm_num⟩
  | 10 => ⟨((-103829047353/70368744177664), (10615999087/70368744177664)), (7/8796093022208), by norm_num⟩
  | 11 => ⟨((111170288799/281474976710656), (-11366604187/281474976710656)), (31/140737488355328), by norm_num⟩
  | 12 => ⟨((-54555688611/562949953421312), (5578045405/562949953421312)), (63/1125899906842624), by norm_num⟩
  | _ => zero

def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581099171716351/10141204801825835211973625643008), (3959550906241/10141204801825835211973625643008)), (153/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444637807697323/158456325028528675187087900672), (4684888591745/633825300114114700748351602688)), (91/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889496554292143/39614081257132168796771975168), (5269452638559/39614081257132168796771975168)), (205/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889255557513175/2475880078570760549798248448), (2798764299497/1237940039285380274899124224)), (217/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885460488113815/77371252455336267181195264), (699513211341/19342813113834066795298816)), (109/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549299689065843/9671406556917033397649408), (5244837437917/9671406556917033397649408)), (51/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((629282891478485/302231454903657293676544), (4587721327391/604462909807314587353088)), (179/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887428180269147/75557863725914323419136), (3726106842263/37778931862957161709568)), (145/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297265111166341/4722366482869645213696), (5586681435757/4722366482869645213696)), (109/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((50658392206783/18446744073709551616), (1919414936095/147573952589676412928)), (75/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1822996652134489/73786976294838206464), (1198879419009/9223372036854775808)), (187/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1822114347796603/9223372036854775808), (10781613162791/9223372036854775808)), (211/4611686018427387904), by norm_num⟩
  | 6 => ⟨((796678409076069/576460752303423488), (10771239862361/1152921504606846976)), (211/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194023576806089/144115188075855872), (1176646253745/18014398509481984)), (185/72057594037927936), by norm_num⟩
  | 4 => ⟨((1490788116412945/36028797018963968), (14096438165739/36028797018963968)), (139/9007199254740992), by norm_num⟩
  | 3 => ⟨((744086266122753/4503599627370496), (8789886056919/4503599627370496)), (697/9007199254740992), by norm_num⟩
  | 2 => ⟨((1112853765542903/2251799813685248), (17518666864047/2251799813685248)), (175/562949953421312), by norm_num⟩
  | 1 => ⟨((1106284289449889/1125899906842624), (6531360445197/281474976710656)), (529/562949953421312), by norm_num⟩
  | 0 => ⟨((1086486571078791/1125899906842624), (51641886052191/1125899906842624)), (537/281474976710656), by norm_num⟩
  | _ => zero

def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((1086486571078791/1125899906842624), (51641886052191/1125899906842624)), (2048493505382449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((261521068076647/281474976710656), (99668212706815/1125899906842624)), (543/140737488355328), by norm_num⟩
  | 2 => ⟨((963103865230715/1125899906842624), (92602680866977/562949953421312)), (4421/562949953421312), by norm_num⟩
  | 3 => ⟨((793381386550019/1125899906842624), (79213080427209/281474976710656)), (36073/2251799813685248), by norm_num⟩
  | 4 => ⟨((234949229294901/562949953421312), (893097984292087/2251799813685248)), (71143/2251799813685248), by norm_num⟩
  | 5 => ⟨((76022953260323/4503599627370496), (186368860872093/562949953421312)), (115817/2251799813685248), by norm_num⟩
  | 6 => ⟨((-984614637802003/9007199254740992), (50335953003109/4503599627370496)), (644755/18014398509481984), by norm_num⟩
  | _ => zero

def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-18969403681/8589934592), (-55722623313/17179869184)), (1/8589934592), by norm_num⟩, -1, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-25733144285/8589934592), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-9649929107/4294967296), (-56693333503/17179869184)), (1/8589934592), by norm_num⟩
  | 1 => ⟨((-25733144285/8589934592), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-940473209711719/9007199254740992), (150223414228801/9007199254740992)), (315345/9007199254740992), by norm_num⟩
  | 1 => ⟨((42990203045/137438953472), (-13733799141/274877906944)), (31/274877906944), by norm_num⟩
  | 2 => ⟨((-32196784677/68719476736), (10285696331/137438953472)), (25/137438953472), by norm_num⟩
  | 3 => ⟨((64301964641/137438953472), (-1283883019/17179869184)), (27/137438953472), by norm_num⟩
  | 4 => ⟨((-24078933841/68719476736), (7692339591/137438953472)), (21/137438953472), by norm_num⟩
  | 5 => ⟨((115414462753/549755813888), (-9217675989/274877906944)), (53/549755813888), by norm_num⟩
  | 6 => ⟨((-14406284621/137438953472), (9204563149/549755813888)), (55/1099511627776), by norm_num⟩
  | 7 => ⟨((49322710607/1099511627776), (-15756803937/2199023255552)), (49/2199023255552), by norm_num⟩
  | 8 => ⟨((-9234852249/549755813888), (11800791521/4398046511104)), (39/4398046511104), by norm_num⟩
  | 9 => ⟨((98364959729/17592186044416), (-15712005339/17592186044416)), (27/8796093022208), by norm_num⟩
  | 10 => ⟨((-117870033779/70368744177664), (18827584591/70368744177664)), (67/70368744177664), by norm_num⟩
  | 11 => ⟨((32100642207/70368744177664), (-5127491163/70368744177664)), (19/70368744177664), by norm_num⟩
  | 12 => ⟨((-64109953241/562949953421312), (640024615/35184372088832)), (5/70368744177664), by norm_num⟩
  | _ => zero

def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790524530142089/5070602400912917605986812821504), (1942974870145/5070602400912917605986812821504)), (19/1267650600228229401496703205376), by norm_num⟩
  | 17 => ⟨((444623093596703/158456325028528675187087900672), (4597512682243/633825300114114700748351602688)), (91/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472357594821447/9903520314283042199192993792), (2585579560417/19807040628566084398385987584)), (51/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1889185294595651/2475880078570760549798248448), (5493093958817/2475880078570760549798248448)), (217/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885425383663473/77371252455336267181195264), (5491673588373/154742504910672534362390528)), (217/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549233925593435/9671406556917033397649408), (5146935063843/9671406556917033397649408)), (51/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258508297267135/604462909807314587353088), (2251029750297/302231454903657293676544)), (179/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887334873501777/75557863725914323419136), (7313018433991/75557863725914323419136)), (145/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648597612542357/2361183241434822606848), (342643101521/295147905179352825856)), (109/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620972609901341/590295810358705651712), (3767064317711/295147905179352825856)), (299/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822876955045817/73786976294838206464), (1176454139027/9223372036854775808)), (187/36893488147419103232), by norm_num⟩
  | 7 => ⟨((910990001456867/4611686018427387904), (10579801979077/9223372036854775808)), (421/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796611432898459/576460752303423488), (5284724790747/576460752303423488)), (211/576460752303423488), by norm_num⟩
  | 5 => ⟨((596953404769457/72057594037927936), (9236627712125/144115188075855872)), (185/72057594037927936), by norm_num⟩
  | 4 => ⟨((1490613846223483/36028797018963968), (1728959336993/4503599627370496)), (139/9007199254740992), by norm_num⟩
  | 3 => ⟨((1487956232654539/9007199254740992), (17248908991561/9007199254740992)), (697/9007199254740992), by norm_num⟩
  | 2 => ⟨((556319883482811/1125899906842624), (8593973969661/1125899906842624)), (699/2251799813685248), by norm_num⟩
  | 1 => ⟨((552984511183981/562949953421312), (6407437390865/281474976710656)), (1057/1125899906842624), by norm_num⟩
  | 0 => ⟨((16966856707735/17592186044416), (50652199257811/1125899906842624)), (1073/562949953421312), by norm_num⟩
  | _ => zero

def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((16966856707735/17592186044416), (50652199257811/1125899906842624)), (4093172313499273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((522500792242259/562949953421312), (12212930851361/140737488355328)), (2167/562949953421312), by norm_num⟩
  | 2 => ⟨((961437461250037/1125899906842624), (181366489341487/1125899906842624)), (8799/1125899906842624), by norm_num⟩
  | 3 => ⟨((1583565613641121/2251799813685248), (77436962206217/281474976710656)), (17863/1125899906842624), by norm_num⟩
  | 4 => ⟨((471601676221855/1125899906842624), (871313763003857/2251799813685248)), (34953/1125899906842624), by norm_num⟩
  | 5 => ⟨((57929168333853/2251799813685248), (729928173278067/2251799813685248)), (56331/1125899906842624), by norm_num⟩
  | 6 => ⟨((-940473209711719/9007199254740992), (150223414228801/9007199254740992)), (315345/9007199254740992), by norm_num⟩
  | _ => zero

def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-9649929107/4294967296), (-56693333503/17179869184)), (1/8589934592), by norm_num⟩, -1, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-6538062151/2147483648), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-19614186453/8589934592), (-28808336353/8589934592)), (1/8589934592), by norm_num⟩
  | 1 => ⟨((-6538062151/2147483648), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-897591712566819/9007199254740992), (96661535066457/4503599627370496)), (616475/18014398509481984), by norm_num⟩
  | 1 => ⟨((83396548731/274877906944), (-17961927025/274877906944)), (31/274877906944), by norm_num⟩
  | 2 => ⟨((-7934458245/17179869184), (13671372463/137438953472)), (25/137438953472), by norm_num⟩
  | 3 => ⟨((32208848211/68719476736), (-13874266739/137438953472)), (27/137438953472), by norm_num⟩
  | 4 => ⟨((-6128785067/17179869184), (21120258197/274877906944)), (43/274877906944), by norm_num⟩
  | 5 => ⟨((7463689461/34359738368), (-6430109997/137438953472)), (7/68719476736), by norm_num⟩
  | 6 => ⟨((-60595653419/549755813888), (13051076109/549755813888)), (15/274877906944), by norm_num⟩
  | 7 => ⟨((26354975209/549755813888), (-11352655443/1099511627776)), (27/1099511627776), by norm_num⟩
  | 8 => ⟨((-40119156685/2199023255552), (2160213389/549755813888)), (43/4398046511104), by norm_num⟩
  | 9 => ⟨((6785759595/1099511627776), (-23384242251/17592186044416)), (15/4398046511104), by norm_num⟩
  | 10 => ⟨((-66110071501/35184372088832), (14238770045/35184372088832)), (19/17592186044416), by norm_num⟩
  | 11 => ⟨((36595199281/70368744177664), (-7881864525/70368744177664)), (11/35184372088832), by norm_num⟩
  | 12 => ⟨((-37138301775/281474976710656), (7998837799/281474976710656)), (47/562949953421312), by norm_num⟩
  | _ => zero

def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197625174288375/1267650600228229401496703205376), (1907970168119/5070602400912917605986812821504)), (153/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778436386153427/633825300114114700748351602688), (564301376331/79228162514264337593543950336)), (91/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472341857194407/9903520314283042199192993792), (5077674445583/39614081257132168796771975168)), (205/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889118455056625/2475880078570760549798248448), (5393769354307/2475880078570760549798248448)), (109/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770783978821901/154742504910672534362390528), (674044029947/19342813113834066795298816)), (109/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774585682786553/4835703278458516698824704), (5053824781791/9671406556917033397649408)), (51/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258453611429549/604462909807314587353088), (2210295756205/302231454903657293676544)), (179/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887246110554797/75557863725914323419136), (7180639587381/75557863725914323419136)), (145/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297128741672399/4722366482869645213696), (5383011349777/4722366482869645213696)), (109/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((405220334853629/147573952589676412928), (7397630634951/590295810358705651712)), (299/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822763083084753/73786976294838206464), (9241025233761/73786976294838206464)), (187/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1821852193899893/9223372036854775808), (10387888515789/9223372036854775808)), (211/4611686018427387904), by norm_num⟩
  | 6 => ⟨((796547713785119/576460752303423488), (10377562059127/1152921504606846976)), (211/576460752303423488), by norm_num⟩
  | 5 => ⟨((596897858844263/72057594037927936), (4534377959249/72057594037927936)), (185/72057594037927936), by norm_num⟩
  | 4 => ⟨((372612010074755/9007199254740992), (13579928090461/36028797018963968)), (555/36028797018963968), by norm_num⟩
  | 3 => ⟨((743875213980231/4503599627370496), (16934336015017/9007199254740992)), (87/1125899906842624), by norm_num⟩
  | 2 => ⟨((1112436135277513/2251799813685248), (8436773558855/1125899906842624)), (699/2251799813685248), by norm_num⟩
  | 1 => ⟨((69104311632029/70368744177664), (6289650539905/281474976710656)), (1057/1125899906842624), by norm_num⟩
  | 0 => ⟨((542650137137421/562949953421312), (12427964844701/281474976710656)), (67/35184372088832), by norm_num⟩
  | _ => zero

def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((542650137137421/562949953421312), (12427964844701/281474976710656)), (255584851014603/134217728000000000000000000), by norm_num⟩
  | 1 => ⟨((65248107826607/70368744177664), (5989907971685/70368744177664)), (1081/281474976710656), by norm_num⟩
  | 2 => ⟨((29995110945743/35184372088832), (22216122556981/140737488355328)), (2189/281474976710656), by norm_num⟩
  | 3 => ⟨((395111521495781/562949953421312), (606064587264763/2251799813685248)), (8847/562949953421312), by norm_num⟩
  | 4 => ⟨((236532520987761/562949953421312), (53171489699831/140737488355328)), (68725/2251799813685248), by norm_num⟩
  | 5 => ⟨((76115586114425/2251799813685248), (1429815086268695/4503599627370496)), (54841/1125899906842624), by norm_num⟩
  | 6 => ⟨((-897591712566819/9007199254740992), (96661535066457/4503599627370496)), (616475/18014398509481984), by norm_num⟩
  | _ => zero

def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-19614186453/8589934592), (-28808336353/8589934592)), (1/8589934592), by norm_num⟩, -1, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨2,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 12 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨2,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 12 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨2,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 12 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨2,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 12 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨2,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 12 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨2,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiRectangle.Tile002Terms2
