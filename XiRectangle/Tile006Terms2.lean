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
namespace Reinmann.XiRectangle.Tile006Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨6,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (1833/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (1833/640))
  have he : value ((3/4), (1833/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-17862266831/8589934592), (-17052882865/2147483648)), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((-24425406505857/2251799813685248), (-1121652794975433/9007199254740992)), (181295/2251799813685248), by norm_num⟩
  | 1 => ⟨((4133398841/137438953472), (47453031763/137438953472)), (1/4294967296), by norm_num⟩
  | 2 => ⟨((-2865053753/68719476736), (-65783870351/137438953472)), (23/68719476736), by norm_num⟩
  | 3 => ⟨((661967977/17179869184), (3799825355/8589934592)), (87/274877906944), by norm_num⟩
  | 4 => ⟨((-3670729895/137438953472), (-42141411703/137438953472)), (31/137438953472), by norm_num⟩
  | 5 => ⟨((8141939447/549755813888), (93472642261/549755813888)), (71/549755813888), by norm_num⟩
  | 6 => ⟨((-7524749829/1099511627776), (-43193532295/549755813888)), (67/1099511627776), by norm_num⟩
  | 7 => ⟨((5960867575/2199023255552), (8554135751/274877906944)), (55/2199023255552), by norm_num⟩
  | 8 => ⟨((-8263517107/8796093022208), (-94868401247/8796093022208)), (79/8796093022208), by norm_num⟩
  | 9 => ⟨((10182815261/35184372088832), (14612836633/4398046511104)), (99/35184372088832), by norm_num⟩
  | 10 => ⟨((-5646551751/70368744177664), (-32412308839/35184372088832)), (57/70368744177664), by norm_num⟩
  | 11 => ⟨((5692932983/281474976710656), (32678546163/140737488355328)), (59/281474976710656), by norm_num⟩
  | 12 => ⟨((-10522774523/2251799813685248), (-120805558067/2251799813685248)), (7/140737488355328), by norm_num⟩
  | _ => zero

def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581267062326477/10141204801825835211973625643008), (-269914498803/1267650600228229401496703205376)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((444689539020525/158456325028528675187087900672), (-2555417872667/633825300114114700748351602688)), (181/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944864882453221/19807040628566084398385987584), (-2874318044911/39614081257132168796771975168)), (51/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1889503898101327/2475880078570760549798248448), (-95416082491/77371252455336267181195264)), (433/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((110698121242039/9671406556917033397649408), (-3052585510503/154742504910672534362390528)), (433/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774766876998333/4835703278458516698824704), (-2861024411055/9671406556917033397649408)), (203/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258771250740655/604462909807314587353088), (-2502622073645/604462909807314587353088)), (89/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((14748150809207/590295810358705651712), (-4065309548681/75557863725914323419136)), (577/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162189691985405/590295810358705651712), (-761928180213/1180591620717411303424)), (433/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621417391068417/590295810358705651712), (-4188543022145/590295810358705651712)), (149/147573952589676412928), by norm_num⟩
  | 8 => ⟨((911717666804429/36893488147419103232), (-5232587349779/73786976294838206464)), (745/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911305737902615/4611686018427387904), (-183825391671/288230376151711744)), (419/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1593858451128663/1152921504606846976), (-5877105955739/1152921504606846976)), (839/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194467561085111/144115188075855872), (-5136502918543/144115188075855872)), (735/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491464172057497/36028797018963968), (-7692837553349/36028797018963968)), (1103/36028797018963968), by norm_num⟩
  | 3 => ⟨((1489035169398467/9007199254740992), (-599701324479/562949953421312)), (1381/9007199254740992), by norm_num⟩
  | 2 => ⟨((1113742612254705/2251799813685248), (-4782019951797/1125899906842624)), (2767/4503599627370496), by norm_num⟩
  | 1 => ⟨((2215365176306605/2251799813685248), (-28536614191165/2251799813685248)), (521/281474976710656), by norm_num⟩
  | 0 => ⟨((544770160407273/562949953421312), (-28226804160231/1125899906842624)), (1051/281474976710656), by norm_num⟩
  | _ => zero

def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((544770160407273/562949953421312), (-28226804160231/1125899906842624)), (4009247899913699/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((526823632810453/562949953421312), (-109261013606625/2251799813685248)), (16695/2251799813685248), by norm_num⟩
  | 2 => ⟨((1966761097230619/2251799813685248), (-204498761436847/2251799813685248)), (8217/562949953421312), by norm_num⟩
  | 3 => ⟨((849615815512591/1125899906842624), (-11163298297585/70368744177664)), (31693/1125899906842624), by norm_num⟩
  | 4 => ⟨((1225587651588753/2251799813685248), (-539132246724023/2251799813685248)), (1809/35184372088832), by norm_num⟩
  | 5 => ⟨((268985170197387/1125899906842624), (-586867287351701/2251799813685248)), (90733/1125899906842624), by norm_num⟩
  | 6 => ⟨((-24425406505857/2251799813685248), (-1121652794975433/9007199254740992)), (181295/2251799813685248), by norm_num⟩
  | _ => zero

def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-17862266831/8589934592), (-17052882865/2147483648)), (1/4294967296), by norm_num⟩, -1, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-18252837983/8589934592), (-69703025047/8589934592)), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((-138559988155931/4503599627370496), (-4060743617347/35184372088832)), (722353/9007199254740992), by norm_num⟩
  | 1 => ⟨((5990142935/68719476736), (89882445339/274877906944)), (65/274877906944), by norm_num⟩
  | 2 => ⟨((-265177389/2147483648), (-31832017941/68719476736)), (3/8589934592), by norm_num⟩
  | 3 => ⟨((4006955291/34359738368), (60124598665/137438953472)), (47/137438953472), by norm_num⟩
  | 4 => ⟨((-22705118399/274877906944), (-85172907621/274877906944)), (69/274877906944), by norm_num⟩
  | 5 => ⟨((12865688885/274877906944), (96525207369/549755813888)), (5/34359738368), by norm_num⟩
  | 6 => ⟨((-6075206905/274877906944), (-91158835185/1099511627776)), (39/549755813888), by norm_num⟩
  | 7 => ⟨((19671265453/2199023255552), (18448030591/549755813888)), (65/2199023255552), by norm_num⟩
  | 8 => ⟨((-435413217/137438953472), (-104534412883/8796093022208)), (95/8796093022208), by norm_num⟩
  | 9 => ⟨((17544796965/17592186044416), (65815176331/17592186044416)), (31/8796093022208), by norm_num⟩
  | 10 => ⟨((-621351911/2199023255552), (-74587374329/70368744177664)), (9/8796093022208), by norm_num⟩
  | 11 => ⟨((20484916661/281474976710656), (38422171681/140737488355328)), (19/70368744177664), by norm_num⟩
  | 12 => ⟨((-4836511603/281474976710656), (-18143034919/281474976710656)), (37/562949953421312), by norm_num⟩
  | _ => zero

def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581207834572467/10141204801825835211973625643008), (-1192745988047/5070602400912917605986812821504)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((889343647835053/316912650057057350374175801344), (-1411435708683/316912650057057350374175801344)), (181/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944825009245639/19807040628566084398385987584), (-3175134762173/39614081257132168796771975168)), (407/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944709564467653/1237940039285380274899124224), (-3372848773001/2475880078570760549798248448)), (433/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885542563666567/77371252455336267181195264), (-3372025573843/154742504910672534362390528)), (433/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549454196198031/9671406556917033397649408), (-790099885259/2417851639229258349412352)), (203/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258701591670625/604462909807314587353088), (-1382237702675/302231454903657293676544)), (89/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1887650021445819/75557863725914323419136), (-4490633934579/75557863725914323419136)), (577/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324358124751705/1180591620717411303424), (-3366542189487/4722366482869645213696)), (433/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621300343223799/590295810358705651712), (-2313333710985/295147905179352825856)), (149/147573952589676412928), by norm_num⟩
  | 8 => ⟨((455822210229505/18446744073709551616), (-5779843826461/73786976294838206464)), (745/73786976294838206464), by norm_num⟩
  | 7 => ⟨((227805802573429/1152921504606846976), (-1624381916743/2305843009213693952)), (419/4611686018427387904), by norm_num⟩
  | 6 => ⟨((398423270755931/288230376151711744), (-3245767983503/576460752303423488)), (839/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149290314134761/18014398509481984), (-5673358940445/144115188075855872)), (735/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491245900919119/36028797018963968), (-4248291211395/18014398509481984)), (69/2251799813685248), by norm_num⟩
  | 3 => ⟨((1488761113070081/9007199254740992), (-10597211698663/9007199254740992)), (691/4503599627370496), by norm_num⟩
  | 2 => ⟨((2226933483847545/4503599627370496), (-5281000230387/1125899906842624)), (2771/4503599627370496), by norm_num⟩
  | 1 => ⟨((2214528579760977/2251799813685248), (-15755193810121/1125899906842624)), (261/140737488355328), by norm_num⟩
  | 0 => ⟨((2177372010857147/2251799813685248), (-62320971782423/2251799813685248)), (4215/1125899906842624), by norm_num⟩
  | _ => zero

def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((2177372010857147/2251799813685248), (-62320971782423/2251799813685248)), (16078953269576671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((131479964974873/140737488355328), (-60261102618349/1125899906842624)), (8385/1125899906842624), by norm_num⟩
  | 2 => ⟨((489712890531469/562949953421312), (-56297208044553/562949953421312)), (16565/1125899906842624), by norm_num⟩
  | 3 => ⟨((840747345588521/1125899906842624), (-97946427787397/562949953421312)), (64267/2251799813685248), by norm_num⟩
  | 4 => ⟨((593731364738745/1125899906842624), (-585119147246841/2251799813685248)), (118345/2251799813685248), by norm_num⟩
  | 5 => ⟨((237077761294393/1125899906842624), (-154278185706519/562949953421312)), (186319/2251799813685248), by norm_num⟩
  | 6 => ⟨((-138559988155931/4503599627370496), (-4060743617347/35184372088832)), (722353/9007199254740992), by norm_num⟩
  | _ => zero

def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-18252837983/8589934592), (-69703025047/8589934592)), (1/4294967296), by norm_num⟩, -1, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-4655269565/2147483648), (-35554621303/4294967296)), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((-424253020549917/9007199254740992), (-58708998514173/562949953421312)), (356393/4503599627370496), by norm_num⟩
  | 1 => ⟨((73090133/536870912), (10357106399/34359738368)), (65/274877906944), by norm_num⟩
  | 2 => ⟨((-13520489997/68719476736), (-59871775659/137438953472)), (49/137438953472), by norm_num⟩
  | 3 => ⟨((13026414147/68719476736), (57683896487/137438953472)), (49/137438953472), by norm_num⟩
  | 4 => ⟨((-37651179557/274877906944), (-41681976323/137438953472)), (73/274877906944), by norm_num⟩
  | 5 => ⟨((21765181209/274877906944), (48190562871/274877906944)), (11/68719476736), by norm_num⟩
  | 6 => ⟨((-20969821691/549755813888), (-92859094613/1099511627776)), (11/137438953472), by norm_num⟩
  | 7 => ⟨((17317308681/1099511627776), (76684944153/2199023255552)), (75/2199023255552), by norm_num⟩
  | 8 => ⟨((-25026729967/4398046511104), (-55411999209/4398046511104)), (7/549755813888), by norm_num⟩
  | 9 => ⟨((32149579329/17592186044416), (17795697507/4398046511104)), (37/8796093022208), by norm_num⟩
  | 10 => ⟨((-2323105903/4398046511104), (-41148945189/35184372088832)), (11/8796093022208), by norm_num⟩
  | 11 => ⟨((39066994575/281474976710656), (5406170411/17592186044416)), (95/281474976710656), by norm_num⟩
  | 12 => ⟨((-18819689631/562949953421312), (-83337825463/1125899906842624)), (47/562949953421312), by norm_num⟩
  | _ => zero

def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790575996580325/5070602400912917605986812821504), (-2598736367653/10141204801825835211973625643008)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((111163776329027/39614081257132168796771975168), (-768749133731/158456325028528675187087900672)), (363/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889574754474643/39614081257132168796771975168), (-3458708495593/39614081257132168796771975168)), (407/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944669559870915/1237940039285380274899124224), (-1837032137131/1237940039285380274899124224)), (433/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771005071872029/154742504910672534362390528), (-3673149294073/154742504910672534362390528)), (433/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774689547544263/4835703278458516698824704), (-1721302764569/4835703278458516698824704)), (203/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314658957283827/151115727451828646838272), (-1505654082611/302231454903657293676544)), (89/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((235942883179581/9444732965739290427392), (-611444304651/9444732965739290427392)), (289/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648676100851701/2361183241434822606848), (-3667072718149/4722366482869645213696)), (217/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621189804149413/590295810358705651712), (-2519818612401/295147905179352825856)), (149/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1823150472000915/73786976294838206464), (-6295666707995/73786976294838206464)), (745/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911145243947793/4611686018427387904), (-3538646624223/4611686018427387904)), (839/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593536816605981/1152921504606846976), (-7070632937907/1152921504606846976)), (105/144115188075855872), by norm_num⟩
  | 5 => ⟨((1194185405687015/144115188075855872), (-193103658463/4503599627370496)), (23/4503599627370496), by norm_num⟩
  | 4 => ⟨((1491039494191805/36028797018963968), (-9254017351065/36028797018963968)), (69/2251799813685248), by norm_num⟩
  | 3 => ⟨((93031362895303/562949953421312), (-2885344757721/2251799813685248)), (173/1125899906842624), by norm_num⟩
  | 2 => ⟨((2226411001423205/4503599627370496), (-23004467183727/4503599627370496)), (2775/4503599627370496), by norm_num⟩
  | 1 => ⟨((1106867637376433/1125899906842624), (-268058227741/17592186044416)), (4183/2251799813685248), by norm_num⟩
  | 0 => ⟨((2175747618758145/2251799813685248), (-33922395544543/1125899906842624)), (2113/562949953421312), by norm_num⟩
  | _ => zero

def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((2175747618758145/2251799813685248), (-33922395544543/1125899906842624)), (8060457469749273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((525054975592389/562949953421312), (-131106807772261/2251799813685248)), (16843/2251799813685248), by norm_num⟩
  | 2 => ⟨((487802536504595/562949953421312), (-1910646134497/17592186044416)), (33381/2251799813685248), by norm_num⟩
  | 3 => ⟨((1664184397906027/2251799813685248), (-423832730471229/2251799813685248)), (32551/1125899906842624), by norm_num⟩
  | 4 => ⟨((575067888156677/1125899906842624), (-313232025815737/1125899906842624)), (120735/2251799813685248), by norm_num⟩
  | 5 => ⟨((826321318898059/4503599627370496), (-1279898353266827/4503599627370496)), (190513/2251799813685248), by norm_num⟩
  | 6 => ⟨((-424253020549917/9007199254740992), (-58708998514173/562949953421312)), (356393/4503599627370496), by norm_num⟩
  | _ => zero

def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-4655269565/2147483648), (-35554621303/4294967296)), (1/4294967296), by norm_num⟩, -1, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-18969403681/8589934592), (-72439410307/8589934592)), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((-541640010504845/9007199254740992), (-51774258982401/562949953421312)), (87187/1125899906842624), by norm_num⟩
  | 1 => ⟨((24335112909/137438953472), (9304574357/34359738368)), (65/274877906944), by norm_num⟩
  | 2 => ⟨((-17913313753/68719476736), (-54793502843/137438953472)), (25/68719476736), by norm_num⟩
  | 3 => ⟨((17581553087/68719476736), (53778708525/137438953472)), (51/137438953472), by norm_num⟩
  | 4 => ⟨((-3235488139/17179869184), (-79174062815/274877906944)), (77/274877906944), by norm_num⟩
  | 5 => ⟨((15242715829/137438953472), (23312319669/137438953472)), (47/274877906944), by norm_num⟩
  | 6 => ⟨((-14960415545/274877906944), (-2860070947/34359738368)), (3/34359738368), by norm_num⟩
  | 7 => ⟨((6292861525/274877906944), (76994782899/2199023255552)), (83/2199023255552), by norm_num⟩
  | 8 => ⟨((-18528946765/2199023255552), (-28338304995/2199023255552)), (63/4398046511104), by norm_num⟩
  | 9 => ⟨((3030964061/1099511627776), (74169253183/17592186044416)), (21/4398046511104), by norm_num⟩
  | 10 => ⟨((-14279181961/17592186044416), (-21838684013/17592186044416)), (51/35184372088832), by norm_num⟩
  | 11 => ⟨((30577585423/140737488355328), (11691394993/35184372088832)), (7/17592186044416), by norm_num⟩
  | 12 => ⟨((-3751409767/70368744177664), (-22949732759/281474976710656)), (57/562949953421312), by norm_num⟩
  | _ => zero

def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581099171716351/10141204801825835211973625643008), (-2800448258005/10141204801825835211973625643008)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((889278552527761/316912650057057350374175801344), (-3313453572479/633825300114114700748351602688)), (363/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889503491978465/39614081257132168796771975168), (-1863453538619/19807040628566084398385987584)), (51/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1889263360121251/2475880078570760549798248448), (-1979472818149/1237940039285380274899124224)), (433/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770929263689071/154742504910672534362390528), (-1978970537739/77371252455336267181195264)), (217/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549307973366879/9671406556917033397649408), (-3709502660405/9671406556917033397649408)), (203/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258573546132069/604462909807314587353088), (-3244748008795/604462909807314587353088)), (89/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((943720879556569/37778931862957161709568), (-5270715820979/75557863725914323419136)), (289/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324319034421527/1180591620717411303424), (-3951287726483/4722366482869645213696)), (217/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810542539695679/295147905179352825856), (-678772422915/73786976294838206464)), (149/147573952589676412928), by norm_num⟩
  | 8 => ⟨((911509680661351/36893488147419103232), (-1695866077963/18446744073709551616)), (373/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1822142707479867/9223372036854775808), (-7625543122679/9223372036854775808)), (105/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1593388685963671/1152921504606846976), (-119034844911/18014398509481984)), (841/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597027699304197/72057594037927936), (-3328865324053/72057594037927936)), (23/4503599627370496), by norm_num⟩
  | 4 => ⟨((93177731320713/2251799813685248), (-2492542729439/9007199254740992)), (1105/36028797018963968), by norm_num⟩
  | 3 => ⟨((1488255702665275/9007199254740992), (-97140675199/70368744177664)), (173/1125899906842624), by norm_num⟩
  | 2 => ⟨((1112957367396669/2251799813685248), (-6195509413309/1125899906842624)), (1389/2251799813685248), by norm_num⟩
  | 1 => ⟨((553245205784827/562949953421312), (-18479315500071/1125899906842624)), (2095/1125899906842624), by norm_num⟩
  | 0 => ⟨((2174199086009875/2251799813685248), (-18265658542969/562949953421312)), (8471/2251799813685248), by norm_num⟩
  | _ => zero

def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((2174199086009875/2251799813685248), (-18265658542969/562949953421312)), (32314309127043967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((524225498243385/562949953421312), (-17636193887279/281474976710656)), (16909/2251799813685248), by norm_num⟩
  | 2 => ⟨((485954799368227/562949953421312), (-131384219453079/1125899906842624)), (8403/562949953421312), by norm_num⟩
  | 3 => ⟨((1647298217823519/2251799813685248), (-453658742603637/2251799813685248)), (65875/2251799813685248), by norm_num⟩
  | 4 => ⟨((1113680331822943/2251799813685248), (-663745714560653/2251799813685248)), (122925/2251799813685248), by norm_num⟩
  | 5 => ⟨((710298937793067/4503599627370496), (-1313083948485109/4503599627370496)), (388117/4503599627370496), by norm_num⟩
  | 6 => ⟨((-541640010504845/9007199254740992), (-51774258982401/562949953421312)), (87187/1125899906842624), by norm_num⟩
  | _ => zero

def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-18969403681/8589934592), (-72439410307/8589934592)), (1/4294967296), by norm_num⟩, -1, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-9649929107/4294967296), (-36850666777/4294967296)), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((-316133722602427/4503599627370496), (-712246312803459/9007199254740992)), (677883/9007199254740992), by norm_num⟩
  | 1 => ⟨((28901733263/137438953472), (65115334045/274877906944)), (1/4294967296), by norm_num⟩
  | 2 => ⟨((-43290927549/137438953472), (-24383513463/68719476736)), (25/68719476736), by norm_num⟩
  | 3 => ⟨((43229342937/137438953472), (48697652149/137438953472)), (13/34359738368), by norm_num⟩
  | 4 => ⟨((-16187942225/68719476736), (-36471282047/137438953472)), (41/137438953472), by norm_num⟩
  | 5 => ⟨((38795792773/274877906944), (21851639337/137438953472)), (51/274877906944), by norm_num⟩
  | 6 => ⟨((-38740602829/549755813888), (-43641107461/549755813888)), (53/549755813888), by norm_num⟩
  | 7 => ⟨((16579496313/549755813888), (4669181217/137438953472)), (47/1099511627776), by norm_num⟩
  | 8 => ⟨((-6208466523/549755813888), (-55950467451/4398046511104)), (73/4398046511104), by norm_num⟩
  | 9 => ⟨((33064717391/8796093022208), (37247249125/8796093022208)), (25/4398046511104), by norm_num⟩
  | 10 => ⟨((-19810608201/17592186044416), (-22316557261/17592186044416)), (31/17592186044416), by norm_num⟩
  | 11 => ⟨((43161656979/140737488355328), (24310702117/70368744177664)), (69/140737488355328), by norm_num⟩
  | 12 => ⟨((-5387532033/70368744177664), (-6069029577/70368744177664)), (71/562949953421312), by norm_num⟩
  | _ => zero

def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790524530142089/5070602400912917605986812821504), (-1495905644739/5070602400912917605986812821504)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((111156061548069/39614081257132168796771975168), (-1769823500757/316912650057057350374175801344)), (363/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944717911883645/19807040628566084398385987584), (-124415952465/1237940039285380274899124224)), (51/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1889191417811473/2475880078570760549798248448), (-2114585749219/1237940039285380274899124224)), (433/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770857271000459/154742504910672534362390528), (-16515935417/604462909807314587353088)), (433/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387310106685901/2417851639229258349412352), (-3962664478031/9671406556917033397649408)), (203/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629257194707515/302231454903657293676544), (-3466171690265/604462909807314587353088)), (89/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((235918191175163/9444732965739290427392), (-5630355131501/75557863725914323419136)), (289/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648601938990165/2361183241434822606848), (-2110432420729/2361183241434822606848)), (217/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810492790229061/295147905179352825856), (-5800600379513/590295810358705651712)), (149/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1822894775289039/73786976294838206464), (-1811529839657/18446744073709551616)), (373/36893488147419103232), by norm_num⟩
  | 7 => ⟨((911001128409821/4611686018427387904), (-4072759913219/4611686018427387904)), (105/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1593247872035575/1152921504606846976), (-4068784629943/576460752303423488)), (105/144115188075855872), by norm_num⟩
  | 5 => ⟨((1193931779046115/144115188075855872), (-3555717794151/72057594037927936)), (737/144115188075855872), by norm_num⟩
  | 4 => ⟨((372664365071311/9007199254740992), (-2662323884631/9007199254740992)), (1107/36028797018963968), by norm_num⟩
  | 3 => ⟨((744010744385267/4503599627370496), (-3320101715945/2251799813685248)), (693/4503599627370496), by norm_num⟩
  | 2 => ⟨((139090131099481/281474976710656), (-13233665366635/2251799813685248)), (1391/2251799813685248), by norm_num⟩
  | 1 => ⟨((1106130722664241/1125899906842624), (-19733915033213/1125899906842624)), (1049/562949953421312), by norm_num⟩
  | 0 => ⟨((2172719248895503/2251799813685248), (-78006245148939/2251799813685248)), (8491/2251799813685248), by norm_num⟩
  | _ => zero

def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((2172719248895503/2251799813685248), (-78006245148939/2251799813685248)), (32390603072356467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2093713629242623/2251799813685248), (-75266757435149/1125899906842624)), (16975/2251799813685248), by norm_num⟩
  | 2 => ⟨((968331286749693/1125899906842624), (-279930808970033/2251799813685248)), (33837/2251799813685248), by norm_num⟩
  | 3 => ⟨((1630829100999275/2251799813685248), (-240754758752035/1125899906842624)), (66617/2251799813685248), by norm_num⟩
  | 4 => ⟨((269534632526447/562949953421312), (-697450749201917/2251799813685248)), (15623/281474976710656), by norm_num⟩
  | 5 => ⟨((600359888501915/4503599627370496), (-333932226566407/1125899906842624)), (394211/4503599627370496), by norm_num⟩
  | 6 => ⟨((-316133722602427/4503599627370496), (-712246312803459/9007199254740992)), (677883/9007199254740992), by norm_num⟩
  | _ => zero

def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-9649929107/4294967296), (-36850666777/4294967296)), (1/4294967296), by norm_num⟩, -1, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-19614186453/8589934592), (-74901674517/8589934592)), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((-349623773106861/4503599627370496), (-595060972530009/9007199254740992)), (163681/2251799813685248), by norm_num⟩
  | 1 => ⟨((64968104369/274877906944), (27643989299/137438953472)), (63/274877906944), by norm_num⟩
  | 2 => ⟨((-6181151609/17179869184), (-42081372845/137438953472)), (25/68719476736), by norm_num⟩
  | 3 => ⟨((12545769843/34359738368), (10676473653/34359738368)), (53/137438953472), by norm_num⟩
  | 4 => ⟨((-19097938893/68719476736), (-4063095449/17179869184)), (21/68719476736), by norm_num⟩
  | 5 => ⟨((46515282779/274877906944), (9896148209/68719476736)), (53/274877906944), by norm_num⟩
  | 6 => ⟨((-47205607373/549755813888), (-40172060359/549755813888)), (7/68719476736), by norm_num⟩
  | 7 => ⟨((41062437381/1099511627776), (34944211181/1099511627776)), (25/549755813888), by norm_num⟩
  | 8 => ⟨((-62507755977/4398046511104), (-53194217505/4398046511104)), (39/2199023255552), by norm_num⟩
  | 9 => ⟨((42290281245/8796093022208), (35989108611/8796093022208)), (55/8796093022208), by norm_num⟩
  | 10 => ⟨((-51501484059/35184372088832), (-2739241217/2199023255552)), (69/35184372088832), by norm_num⟩
  | 11 => ⟨((7127155627/17592186044416), (24260891193/70368744177664)), (39/70368744177664), by norm_num⟩
  | 12 => ⟨((-57863427263/562949953421312), (-6155235633/70368744177664)), (81/562949953421312), by norm_num⟩
  | _ => zero

def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197625174288375/1267650600228229401496703205376), (-3173835739877/10141204801825835211973625643008)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((1778439750913693/633825300114114700748351602688), (-3754775428227/633825300114114700748351602688)), (363/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889371401921461/39614081257132168796771975168), (-4223267074905/39614081257132168796771975168)), (51/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((944561461745211/1237940039285380274899124224), (-4486174428247/2475880078570760549798248448)), (433/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770788724869093/154742504910672534362390528), (-2242498472677/77371252455336267181195264)), (433/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549176109748897/9671406556917033397649408), (-4203433834003/9671406556917033397649408)), (203/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629229028553247/302231454903657293676544), (-3676754109599/604462909807314587353088)), (89/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1887253886514863/75557863725914323419136), (-1493095350591/18889465931478580854784)), (289/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297135055914977/4722366482869645213696), (-4477235682007/4722366482869645213696)), (217/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((405222701065521/147573952589676412928), (-1538217108987/147573952589676412928)), (597/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822776086665685/73786976294838206464), (-1921522936779/18446744073709551616)), (373/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1821868432507247/9223372036854775808), (-2159997556365/2305843009213693952)), (105/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1593113674196743/1152921504606846976), (-4315708355901/576460752303423488)), (841/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193813937075859/144115188075855872), (-7542851604381/144115188075855872)), (737/144115188075855872), by norm_num⟩
  | 4 => ⟨((745239931495903/18014398509481984), (-11295019335359/36028797018963968)), (1107/36028797018963968), by norm_num⟩
  | 3 => ⟨((743899019831207/4503599627370496), (-7042556489979/4503599627370496)), (1387/9007199254740992), by norm_num⟩
  | 2 => ⟨((556247718057079/1125899906842624), (-14034702097937/2251799813685248)), (1393/2251799813685248), by norm_num⟩
  | 1 => ⟨((138223368451595/140737488355328), (-2615788654489/140737488355328)), (1051/562949953421312), by norm_num⟩
  | 0 => ⟨((1085650966324167/1125899906842624), (-41351343670399/1125899906842624)), (4255/1125899906842624), by norm_num⟩
  | _ => zero

def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((1085650966324167/1125899906842624), (-41351343670399/1125899906842624)), (16231541160201671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((32666316514475/35184372088832), (-159492423586625/2251799813685248)), (8519/1125899906842624), by norm_num⟩
  | 2 => ⟨((964862762095687/1125899906842624), (-296155917029717/2251799813685248)), (34051/2251799813685248), by norm_num⟩
  | 3 => ⟨((1614767107371389/2251799813685248), (-507593640215507/2251799813685248)), (67319/2251799813685248), by norm_num⟩
  | 4 => ⟨((1043530376537187/2251799813685248), (-363995728727543/1125899906842624)), (31725/562949953421312), by norm_num⟩
  | 5 => ⟨((124119400230663/1125899906842624), (-1349464894875683/4503599627370496)), (399337/4503599627370496), by norm_num⟩
  | 6 => ⟨((-349623773106861/4503599627370496), (-595060972530009/9007199254740992)), (163681/2251799813685248), by norm_num⟩
  | _ => zero

def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-19614186453/8589934592), (-74901674517/8589934592)), (1/4294967296), by norm_num⟩, -1, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨6,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 12 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨6,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 12 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨6,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 12 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨6,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 12 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨6,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 12 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨6,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiRectangle.Tile006Terms2
