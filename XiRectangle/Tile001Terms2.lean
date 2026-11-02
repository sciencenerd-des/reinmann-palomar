/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 38 bits, checked against fixed final error disks.
module

public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile001Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨1,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (423/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (423/640))
  have he : value ((3/4), (423/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-381061692393/137438953472), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-285796269295/137438953472), (-62964490579/34359738368)), (1/68719476736), by norm_num⟩
  | 1 => ⟨((-381061692393/137438953472), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-291308791112619/9007199254740992), (-1087561395252165/9007199254740992)), (11849/2251799813685248), by norm_num⟩
  | 1 => ⟨((24648421293/274877906944), (368085993557/1099511627776)), (9/549755813888), by norm_num⟩
  | 2 => ⟨((-34169967449/274877906944), (-127568884319/274877906944)), (7/274877906944), by norm_num⟩
  | 3 => ⟨((31579755463/274877906944), (29474670831/68719476736)), (15/549755813888), by norm_num⟩
  | 4 => ⟨((-10944709231/137438953472), (-326884559751/1099511627776)), (23/1099511627776), by norm_num⟩
  | 5 => ⟨((97104567623/2199023255552), (2832238887/17179869184)), (7/549755813888), by norm_num⟩
  | 6 => ⟨((-89743676357/4398046511104), (-167522850065/2199023255552)), (7/1099511627776), by norm_num⟩
  | 7 => ⟨((71092087131/8796093022208), (265412551319/8796093022208)), (3/1099511627776), by norm_num⟩
  | 8 => ⟨((-49277279755/17592186044416), (-5749061301/549755813888)), (35/35184372088832), by norm_num⟩
  | 9 => ⟨((474394549/549755813888), (56674782317/17592186044416)), (3/8796093022208), by norm_num⟩
  | 10 => ⟨((-33671704997/140737488355328), (-62854344915/70368744177664)), (7/70368744177664), by norm_num⟩
  | 11 => ⟨((33948287103/562949953421312), (253482542335/1125899906842624)), (15/562949953421312), by norm_num⟩
  | 12 => ⟨((-62749758641/4503599627370496), (-234267612721/4503599627370496)), (29/4503599627370496), by norm_num⟩
  | _ => zero

def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790633531163243/5070602400912917605986812821504), (-9324398775/39614081257132168796771975168)), (5/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((889378689944723/316912650057057350374175801344), (-2824922456517/633825300114114700748351602688)), (3/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((944864423953159/19807040628566084398385987584), (-3177453726653/39614081257132168796771975168)), (27/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944751433378521/1237940039285380274899124224), (-1687663884349/1237940039285380274899124224)), (7/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1771168844418459/154742504910672534362390528), (-421815192311/19342813113834066795298816)), (7/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1549532658935149/9671406556917033397649408), (-1581378762717/4835703278458516698824704)), (13/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258770224537535/604462909807314587353088), (-1383278322891/302231454903657293676544)), (23/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887761508556833/75557863725914323419136), (-2247024839675/37778931862957161709568)), (37/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297516078209501/4722366482869645213696), (-52642710663/73786976294838206464)), (7/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((810707602962271/295147905179352825856), (-4630278308327/590295810358705651712)), (19/295147905179352825856), by norm_num⟩
  | 8 => ⟨((911716165627879/36893488147419103232), (-5784429128625/73786976294838206464)), (47/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911303863095659/4611686018427387904), (-812848069931/1152921504606846976)), (53/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398463559346205/288230376151711744), (-6496915666117/1152921504606846976)), (53/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194463353050845/144115188075855872), (-5678204021779/144115188075855872)), (47/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491456820829839/36028797018963968), (-4252062476479/18014398509481984)), (35/18014398509481984), by norm_num⟩
  | 3 => ⟨((1489024168186003/9007199254740992), (-5303559598123/4503599627370496)), (11/1125899906842624), by norm_num⟩
  | 2 => ⟨((2227457811019787/4503599627370496), (-10572623459221/2251799813685248)), (87/2251799813685248), by norm_num⟩
  | 1 => ⟨((553827654328091/562949953421312), (-15772904838107/1125899906842624)), (131/1125899906842624), by norm_num⟩
  | 0 => ⟨((2178918300099207/2251799813685248), (-62405882005799/2251799813685248)), (33/140737488355328), by norm_num⟩
  | _ => zero

def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((2178918300099207/2251799813685248), (-62405882005799/2251799813685248)), (125885546636537/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((2106666159028901/2251799813685248), (-120772119714967/2251799813685248)), (263/562949953421312), by norm_num⟩
  | 2 => ⟨((1964409257791793/2251799813685248), (-56494040014445/562949953421312)), (1041/1125899906842624), by norm_num⟩
  | 3 => ⟨((845509996945913/1125899906842624), (-394270981070249/2251799813685248)), (4051/2251799813685248), by norm_num⟩
  | 4 => ⟨((600430597070337/1125899906842624), (-148041603864865/562949953421312)), (469/140737488355328), by norm_num⟩
  | 5 => ⟨((484681869747865/2251799813685248), (-78949032733383/281474976710656)), (11951/2251799813685248), by norm_num⟩
  | 6 => ⟨((-291308791112619/9007199254740992), (-1087561395252165/9007199254740992)), (11849/2251799813685248), by norm_num⟩
  | _ => zero

def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-285796269295/137438953472), (-62964490579/34359738368)), (1/68719476736), by norm_num⟩, 0, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-194696938485/68719476736), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-18252837983/8589934592), (-32170626945/17179869184)), (3/137438953472), by norm_num⟩
  | 1 => ⟨((-194696938485/68719476736), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-319766023747447/9007199254740992), (-128404277020827/1125899906842624)), (68445/9007199254740992), by norm_num⟩
  | 1 => ⟨((27647868819/274877906944), (355270225673/1099511627776)), (13/549755813888), by norm_num⟩
  | 2 => ⟨((-78332310873/549755813888), (-251639086031/549755813888)), (5/137438953472), by norm_num⟩
  | 3 => ⟨((18494345703/137438953472), (237649072143/549755813888)), (5/137438953472), by norm_num⟩
  | 4 => ⟨((-104796854071/1099511627776), (-336655261199/1099511627776)), (15/549755813888), by norm_num⟩
  | 5 => ⟨((29691184537/549755813888), (190763235675/1099511627776)), (9/549755813888), by norm_num⟩
  | 6 => ⟨((-112161946975/4398046511104), (-90078824145/1099511627776)), (9/1099511627776), by norm_num⟩
  | 7 => ⟨((45396960695/4398046511104), (145835729477/4398046511104)), (31/8796093022208), by norm_num⟩
  | 8 => ⟨((-128619274821/35184372088832), (-206591867397/17592186044416)), (47/35184372088832), by norm_num⟩
  | 9 => ⟨((20244769207/17592186044416), (260141704659/70368744177664)), (31/70368744177664), by norm_num⟩
  | 10 => ⟨((-91772400423/281474976710656), (-147407389797/140737488355328)), (37/281474976710656), by norm_num⟩
  | 11 => ⟨((47274688999/562949953421312), (151867848649/562949953421312)), (5/140737488355328), by norm_num⟩
  | 12 => ⟨((-89292853139/4503599627370496), (-143424671775/2251799813685248)), (5/562949953421312), by norm_num⟩
  | _ => zero

def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581207834572467/10141204801825835211973625643008), (-609810136157/2535301200456458802993406410752)), (29/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778687101257139/633825300114114700748351602688), (-360809346799/79228162514264337593543950336)), (35/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889649788836163/39614081257132168796771975168), (-3246674763979/39614081257132168796771975168)), (39/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889418870645193/2475880078570760549798248448), (-862210873101/618970019642690137449562112)), (21/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885542426494625/77371252455336267181195264), (-3448001693151/154742504910672534362390528)), (21/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549453921954645/9671406556917033397649408), (-1615803695953/4835703278458516698824704)), (39/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258701334674195/604462909807314587353088), (-353345314461/75557863725914323419136)), (35/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887649571915477/75557863725914323419136), (-1147953361071/18889465931478580854784)), (55/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297432133963407/4722366482869645213696), (-3442394411609/4722366482869645213696)), (21/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621299796008495/590295810358705651712), (-2365455784073/295147905179352825856)), (57/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823288089065117/73786976294838206464), (-369379377067/4611686018427387904)), (71/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822445481622969/9223372036854775808), (-6643923578055/9223372036854775808)), (79/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398423006964715/288230376151711744), (-1659449048805/288230376151711744)), (5/72057594037927936), by norm_num⟩
  | 5 => ⟨((1194321459374597/144115188075855872), (-5801184040187/144115188075855872)), (35/72057594037927936), by norm_num⟩
  | 4 => ⟨((1491244060222455/36028797018963968), (-8688014981353/36028797018963968)), (105/36028797018963968), by norm_num⟩
  | 3 => ⟨((1488758358584877/9007199254740992), (-10835968734151/9007199254740992)), (131/9007199254740992), by norm_num⟩
  | 2 => ⟨((2226926620552883/4503599627370496), (-21599914999523/4503599627370496)), (261/4503599627370496), by norm_num⟩
  | 1 => ⟨((2214514921763141/2251799813685248), (-32220262276419/2251799813685248)), (49/281474976710656), by norm_num⟩
  | 0 => ⟨((2177331378677299/2251799813685248), (-63724756690113/2251799813685248)), (99/281474976710656), by norm_num⟩
  | _ => zero

def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((2177331378677299/2251799813685248), (-63724756690113/2251799813685248)), (377656103038699/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((2103522284339109/2251799813685248), (-30808669468909/562949953421312)), (1577/2251799813685248), by norm_num⟩
  | 2 => ⟨((979132156437881/1125899906842624), (-230239730494077/2251799813685248)), (195/140737488355328), by norm_num⟩
  | 3 => ⟨((419862898402545/562949953421312), (-200226612016101/1125899906842624)), (3033/1125899906842624), by norm_num⟩
  | 4 => ⟨((590681919075295/1125899906842624), (-597337117784505/2251799813685248)), (11207/2251799813685248), by norm_num⟩
  | 5 => ⟨((461323817283163/2251799813685248), (-313381529675511/1125899906842624)), (35411/4503599627370496), by norm_num⟩
  | 6 => ⟨((-319766023747447/9007199254740992), (-128404277020827/1125899906842624)), (68445/9007199254740992), by norm_num⟩
  | _ => zero

def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-18252837983/8589934592), (-32170626945/17179869184)), (3/137438953472), by norm_num⟩, 0, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-198624834775/68719476736), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-148968626081/68719476736), (-65639300867/34359738368)), (1/34359738368), by norm_num⟩
  | 1 => ⟨((-198624834775/68719476736), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-343298820331443/9007199254740992), (-485927888438029/4503599627370496)), (88041/9007199254740992), by norm_num⟩
  | 1 => ⟨((121125636573/1099511627776), (171449248671/549755813888)), (33/1099511627776), by norm_num⟩
  | 2 => ⟨((-87524529777/549755813888), (-247776033135/549755813888)), (13/274877906944), by norm_num⟩
  | 3 => ⟨((84326142997/549755813888), (29840202019/68719476736)), (27/549755813888), by norm_num⟩
  | 4 => ⟨((-121866951085/1099511627776), (-172498554331/549755813888)), (41/1099511627776), by norm_num⟩
  | 5 => ⟨((140896317455/2199023255552), (398867959773/2199023255552)), (25/1099511627776), by norm_num⟩
  | 6 => ⟨((-135747578921/4398046511104), (-192146114343/2199023255552)), (25/2199023255552), by norm_num⟩
  | 7 => ⟨((112103133805/8796093022208), (158678200653/4398046511104)), (11/2199023255552), by norm_num⟩
  | 8 => ⟨((-20251233245/4398046511104), (-7166234215/549755813888)), (17/8796093022208), by norm_num⟩
  | 9 => ⟨((52029860119/35184372088832), (294586040683/70368744177664)), (23/35184372088832), by norm_num⟩
  | 10 => ⟨((-30077127651/70368744177664), (-42573158613/35184372088832)), (55/281474976710656), by norm_num⟩
  | 11 => ⟨((7903098211/70368744177664), (357970197235/1125899906842624)), (15/281474976710656), by norm_num⟩
  | 12 => ⟨((-60914378317/2251799813685248), (-10777780711/140737488355328)), (15/1125899906842624), by norm_num⟩
  | _ => zero

def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581151993160631/10141204801825835211973625643008), (-1244225394407/5070602400912917605986812821504)), (39/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778620841876283/633825300114114700748351602688), (-2944499352907/633825300114114700748351602688)), (23/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944787625639973/19807040628566084398385987584), (-1655964035147/19807040628566084398385987584)), (13/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1889339678489093/2475880078570760549798248448), (-3518144687361/2475880078570760549798248448)), (55/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771005665343763/154742504910672534362390528), (-439658581563/19342813113834066795298816)), (55/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549379688338445/9671406556917033397649408), (-103015900135/302231454903657293676544)), (51/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((78664774066969/37778931862957161709568), (-2883514904577/604462909807314587353088)), (45/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887544037853955/75557863725914323419136), (-146373998673/2361183241434822606848)), (73/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297352991351051/4722366482869645213696), (-438931340571/590295810358705651712)), (55/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810595493924389/295147905179352825856), (-4825767253749/590295810358705651712)), (75/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823152098333549/73786976294838206464), (-3014247313771/36893488147419103232)), (47/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1822292518931585/9223372036854775808), (-1694238006107/2305843009213693952)), (53/4611686018427387904), by norm_num⟩
  | 6 => ⟨((796769549469353/576460752303423488), (-6770575868233/1152921504606846976)), (53/576460752303423488), by norm_num⟩
  | 5 => ⟨((597093842397093/72057594037927936), (-5917086734037/144115188075855872)), (93/144115188075855872), by norm_num⟩
  | 4 => ⟨((745521737689937/18014398509481984), (-553831928537/2251799813685248)), (139/36028797018963968), by norm_num⟩
  | 3 => ⟨((744253881814007/4503599627370496), (-11051613754995/9007199254740992)), (87/4503599627370496), by norm_num⟩
  | 2 => ⟨((2226425844094917/4503599627370496), (-22028288431355/4503599627370496)), (347/4503599627370496), by norm_num⟩
  | 1 => ⟨((553441202174445/562949953421312), (-16427779190433/1125899906842624)), (523/2251799813685248), by norm_num⟩
  | 0 => ⟨((271979433264887/281474976710656), (-64966457389951/2251799813685248)), (33/70368744177664), by norm_num⟩
  | _ => zero

def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((271979433264887/281474976710656), (-64966457389951/2251799813685248)), (125885278201081/268435456000000000000000000), by norm_num⟩
  | 1 => ⟨((1050279715427905/1125899906842624), (-125549634774887/2251799813685248)), (2103/2251799813685248), by norm_num⟩
  | 2 => ⟨((1952476940909687/2251799813685248), (-58558595609635/562949953421312)), (4159/2251799813685248), by norm_num⟩
  | 3 => ⟨((417144147986957/562949953421312), (-50774632329661/281474976710656)), (4039/1125899906842624), by norm_num⟩
  | 4 => ⟨((1163137050120009/2251799813685248), (-300990745110247/1125899906842624)), (14887/2251799813685248), by norm_num⟩
  | 5 => ⟨((879746127319149/4503599627370496), (-621890960738647/2251799813685248)), (46679/4503599627370496), by norm_num⟩
  | 6 => ⟨((-343298820331443/9007199254740992), (-485927888438029/4503599627370496)), (88041/9007199254740992), by norm_num⟩
  | _ => zero

def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-148968626081/68719476736), (-65639300867/34359738368)), (1/34359738368), by norm_num⟩, 0, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-404680611859/137438953472), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-151755229447/68719476736), (-66867147975/34359738368)), (1/34359738368), by norm_num⟩
  | 1 => ⟨((-404680611859/137438953472), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-362788025078213/9007199254740992), (-920861372043211/9007199254740992)), (85167/9007199254740992), by norm_num⟩
  | 1 => ⟨((130396386989/1099511627776), (165491950577/549755813888)), (33/1099511627776), by norm_num⟩
  | 2 => ⟨((-23996512787/137438953472), (-243640475009/549755813888)), (13/274877906944), by norm_num⟩
  | 3 => ⟨((94208356819/549755813888), (119564085253/274877906944)), (27/549755813888), by norm_num⟩
  | 4 => ⟨((-138695378991/1099511627776), (-352049153127/1099511627776)), (21/549755813888), by norm_num⟩
  | 5 => ⟨((40838008013/549755813888), (103658724905/549755813888)), (13/549755813888), by norm_num⟩
  | 6 => ⟨((-80163348417/2199023255552), (-101738930047/1099511627776)), (27/2199023255552), by norm_num⟩
  | 7 => ⟨((67438882223/4398046511104), (171179469331/4398046511104)), (3/549755813888), by norm_num⟩
  | 8 => ⟨((-24821209191/4398046511104), (-126006875483/8796093022208)), (37/17592186044416), by norm_num⟩
  | 9 => ⟨((129928063737/70368744177664), (329795160725/70368744177664)), (25/35184372088832), by norm_num⟩
  | 10 => ⟨((-76513051071/140737488355328), (-48553086319/35184372088832)), (61/281474976710656), by norm_num⟩
  | 11 => ⟨((81922912723/562949953421312), (207944145333/562949953421312)), (17/281474976710656), by norm_num⟩
  | 12 => ⟨((-80405672503/2251799813685248), (-204092949003/2251799813685248)), (35/2251799813685248), by norm_num⟩
  | _ => zero

def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790549585858185/5070602400912917605986812821504), (-633749921641/2535301200456458802993406410752)), (39/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778558166840005/633825300114114700748351602688), (-2999378311551/633825300114114700748351602688)), (47/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944752372989047/19807040628566084398385987584), (-1686821725177/19807040628566084398385987584)), (13/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((944632385231303/1237940039285380274899124224), (-1791843962889/1237940039285380274899124224)), (55/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885465380834771/77371252455336267181195264), (-3582778881501/154742504910672534362390528)), (55/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549309470776907/9671406556917033397649408), (-1678944792309/4835703278458516698824704)), (13/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258574949348071/604462909807314587353088), (-2937188042703/604462909807314587353088)), (45/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887444213529785/75557863725914323419136), (-4771121129637/75557863725914323419136)), (73/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297278130764453/4722366482869645213696), (-894189541823/1180591620717411303424)), (55/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810544033511623/295147905179352825856), (-153608491005/18446744073709551616)), (75/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823023466091653/73786976294838206464), (-767560673789/9223372036854775808)), (47/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1822147833606779/9223372036854775808), (-3451374780195/4611686018427387904)), (53/4611686018427387904), by norm_num⟩
  | 6 => ⟨((796697223107149/576460752303423488), (-6896133564307/1152921504606846976)), (53/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194061150563807/144115188075855872), (-6026680242251/144115188075855872)), (93/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490853748409683/36028797018963968), (-70509086147/281474976710656)), (139/36028797018963968), by norm_num⟩
  | 3 => ⟨((1488270736346619/9007199254740992), (-11255489239491/9007199254740992)), (87/4503599627370496), by norm_num⟩
  | 2 => ⟨((2225952188901321/4503599627370496), (-22433227940863/4503599627370496)), (347/4503599627370496), by norm_num⟩
  | 1 => ⟨((2213055341992089/2251799813685248), (-33455966007259/2251799813685248)), (523/2251799813685248), by norm_num⟩
  | 0 => ⟨((1087210351104297/1125899906842624), (-33069713965903/1125899906842624)), (1057/2251799813685248), by norm_num⟩
  | _ => zero

def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((1087210351104297/1125899906842624), (-33069713965903/1125899906842624)), (4032143599700217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((262219744044177/281474976710656), (-3991666478663/70368744177664)), (2105/2251799813685248), by norm_num⟩
  | 2 => ⟨((1947008165250383/2251799813685248), (-237990607807827/2251799813685248)), (2081/1125899906842624), by norm_num⟩
  | 3 => ⟨((1658318489704291/2251799813685248), (-411554929384597/2251799813685248)), (4039/1125899906842624), by norm_num⟩
  | 4 => ⟨((1146035601260191/2251799813685248), (-75771516719605/281474976710656)), (3713/562949953421312), by norm_num⟩
  | 5 => ⟨((840174990568421/4503599627370496), (-1234025940592419/4503599627370496)), (46229/4503599627370496), by norm_num⟩
  | 6 => ⟨((-362788025078213/9007199254740992), (-920861372043211/9007199254740992)), (85167/9007199254740992), by norm_num⟩
  | _ => zero

def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-151755229447/68719476736), (-66867147975/34359738368)), (1/34359738368), by norm_num⟩, 0, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-25733144285/8589934592), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-77199432855/34359738368), (-136064000407/68719476736)), (1/68719476736), by norm_num⟩
  | 1 => ⟨((-25733144285/8589934592), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-94732707551287/2251799813685248), (-109220845533603/1125899906842624)), (41241/9007199254740992), by norm_num⟩
  | 1 => ⟨((34642801437/274877906944), (159763873003/549755813888)), (17/1099511627776), by norm_num⟩
  | 2 => ⟨((-103780558311/549755813888), (-59826223813/137438953472)), (15/549755813888), by norm_num⟩
  | 3 => ⟨((103632922633/549755813888), (29870558247/68719476736)), (17/549755813888), by norm_num⟩
  | 4 => ⟨((-155228245467/1099511627776), (-357936781479/1099511627776)), (7/274877906944), by norm_num⟩
  | 5 => ⟨((93004452943/1099511627776), (107228276817/549755813888)), (9/549755813888), by norm_num⟩
  | 6 => ⟨((-92872147089/2199023255552), (-214151472999/2199023255552)), (5/549755813888), by norm_num⟩
  | 7 => ⟨((39745726907/2199023255552), (183297279741/4398046511104)), (9/2199023255552), by norm_num⟩
  | 8 => ⟨((-119067556831/17592186044416), (-4289918567/274877906944)), (29/17592186044416), by norm_num⟩
  | 9 => ⟨((9908181187/4398046511104), (45694035563/8796093022208)), (41/70368744177664), by norm_num⟩
  | 10 => ⟨((-94983226093/140737488355328), (-27377419409/17592186044416)), (13/70368744177664), by norm_num⟩
  | 11 => ⟨((51735330155/281474976710656), (238590309499/562949953421312)), (15/281474976710656), by norm_num⟩
  | 12 => ⟨((-51661732743/1125899906842624), (-238250896775/2251799813685248)), (1/70368744177664), by norm_num⟩
  | _ => zero

def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197631132535527/1267650600228229401496703205376), (-1289580193077/5070602400912917605986812821504)), (5/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((889249354109867/316912650057057350374175801344), (-1525717440699/316912650057057350374175801344)), (23/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889437859020435/39614081257132168796771975168), (-3432184469071/39614081257132168796771975168)), (27/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889193706796897/2475880078570760549798248448), (-1822929705709/1237940039285380274899124224)), (7/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((885429851104907/77371252455336267181195264), (-1822459244727/77371252455336267181195264)), (7/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((774621428505439/4835703278458516698824704), (-3416111609935/9671406556917033397649408)), (27/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258516666789961/604462909807314587353088), (-1494049236109/302231454903657293676544)), (23/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943674756403441/37778931862957161709568), (-4853787153467/75557863725914323419136)), (37/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297207112622613/4722366482869645213696), (-3638702219857/4722366482869645213696)), (7/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1620990429142271/590295810358705651712), (-5000554711059/590295810358705651712)), (39/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455725359225951/18446744073709551616), (-1561676032475/18446744073709551616)), (3/4611686018427387904), by norm_num⟩
  | 7 => ⟨((911005287927113/4611686018427387904), (-7022060169127/9223372036854775808)), (27/4611686018427387904), by norm_num⟩
  | 6 => ⟨((796628609989923/576460752303423488), (-7015212577515/1152921504606846976)), (27/576460752303423488), by norm_num⟩
  | 5 => ⟨((298485278322655/36028797018963968), (-1532653543017/36028797018963968)), (47/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490673764422409/36028797018963968), (-2295136088299/9007199254740992)), (35/18014398509481984), by norm_num⟩
  | 3 => ⟨((1488045883479213/9007199254740992), (-5724404276587/4503599627370496)), (87/9007199254740992), by norm_num⟩
  | 2 => ⟨((1112751434751591/2251799813685248), (-1426072008151/281474976710656)), (87/2251799813685248), by norm_num⟩
  | 1 => ⟨((2212382346088325/2251799813685248), (-8506273187953/562949953421312)), (131/1125899906842624), by norm_num⟩
  | 0 => ⟨((2173078746476709/2251799813685248), (-67250802365389/2251799813685248)), (529/2251799813685248), by norm_num⟩
  | _ => zero

def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((2173078746476709/2251799813685248), (-67250802365389/2251799813685248)), (2017983443450217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((523775308455265/562949953421312), (-16224942423341/281474976710656)), (1053/2251799813685248), by norm_num⟩
  | 2 => ⟨((970912519167815/1125899906842624), (-120767029762509/1125899906842624)), (1041/1125899906842624), by norm_num⟩
  | 3 => ⟨((824306351531531/1125899906842624), (-416570675195985/2251799813685248)), (2019/1125899906842624), by norm_num⟩
  | 4 => ⟨((35310542229989/70368744177664), (-609968703858905/2251799813685248)), (463/140737488355328), by norm_num⟩
  | 5 => ⟨((25110374843605/140737488355328), (-1224312067994419/4503599627370496)), (22897/4503599627370496), by norm_num⟩
  | 6 => ⟨((-94732707551287/2251799813685248), (-109220845533603/1125899906842624)), (41241/9007199254740992), by norm_num⟩
  | _ => zero

def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-77199432855/34359738368), (-136064000407/68719476736)), (1/68719476736), by norm_num⟩, 0, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-418435977663/137438953472), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-19614186453/8589934592), (-138280014493/68719476736)), (1/34359738368), by norm_num⟩
  | 1 => ⟨((-418435977663/137438953472), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-196142455373405/4503599627370496), (-415077474911193/4503599627370496)), (79875/9007199254740992), by norm_num⟩
  | 1 => ⟨((145791041595/1099511627776), (154261802461/549755813888)), (1/34359738368), by norm_num⟩
  | 2 => ⟨((-110966024339/549755813888), (-117413379719/274877906944)), (13/274877906944), by norm_num⟩
  | 3 => ⟨((28153212577/137438953472), (119155889681/274877906944)), (29/549755813888), by norm_num⟩
  | 4 => ⟨((-171426174769/1099511627776), (-362772779721/1099511627776)), (23/549755813888), by norm_num⟩
  | 5 => ⟨((26095541775/274877906944), (220893973531/1099511627776)), (15/549755813888), by norm_num⟩
  | 6 => ⟨((-52965641639/1099511627776), (-224172219591/2199023255552)), (1/68719476736), by norm_num⟩
  | 7 => ⟨((92145762513/4398046511104), (24374905445/549755813888)), (15/2199023255552), by norm_num⟩
  | 8 => ⟨((-35067480189/4398046511104), (-296839786179/17592186044416)), (47/17592186044416), by norm_num⟩
  | 9 => ⟨((94901093573/35184372088832), (50207521635/8796093022208)), (17/17592186044416), by norm_num⟩
  | 10 => ⟨((-115571403499/140737488355328), (-244572681857/140737488355328)), (43/140737488355328), by norm_num⟩
  | 11 => ⟨((31987248283/140737488355328), (270766188207/562949953421312)), (25/281474976710656), by norm_num⟩
  | 12 => ⟨((-64923930079/1125899906842624), (-137392289229/1125899906842624)), (53/2251799813685248), by norm_num⟩
  | _ => zero

def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197625174288375/1267650600228229401496703205376), (-1310583014281/5070602400912917605986812821504)), (39/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778442151980931/633825300114114700748351602688), (-3100944914601/633825300114114700748351602688)), (23/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((236171779640821/4951760157141521099596496896), (-3487861398199/39614081257132168796771975168)), (13/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((944563056070523/1237940039285380274899124224), (-926247183423/618970019642690137449562112)), (55/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885396055812173/77371252455336267181195264), (-231501061385/9671406556917033397649408)), (55/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549179495170253/9671406556917033397649408), (-216967731445/604462909807314587353088)), (13/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258461229522201/604462909807314587353088), (-759129081073/151115727451828646838272)), (23/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887259435409739/75557863725914323419136), (-4932404825649/75557863725914323419136)), (73/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297139561737573/4722366482869645213696), (-3697611834031/4722366482869645213696)), (55/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405224389588195/147573952589676412928), (-5081468322401/590295810358705651712)), (75/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911392682999623/36893488147419103232), (-3173857790609/36893488147419103232)), (47/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1821880020369573/9223372036854775808), (-7135518689333/9223372036854775808)), (53/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1593126695009523/1152921504606846976), (-7128447136583/1152921504606846976)), (53/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193826938490501/144115188075855872), (-6229442787601/144115188075855872)), (23/36028797018963968), by norm_num⟩
  | 4 => ⟨((1490502571869143/36028797018963968), (-1166035607539/4503599627370496)), (139/36028797018963968), by norm_num⟩
  | 3 => ⟨((46494750496895/281474976710656), (-2908151706885/2251799813685248)), (87/4503599627370496), by norm_num⟩
  | 2 => ⟨((2225075508586137/4503599627370496), (-23182124069523/4503599627370496)), (347/4503599627370496), by norm_num⟩
  | 1 => ⟨((552935564341353/562949953421312), (-4320751906225/281474976710656)), (131/562949953421312), by norm_num⟩
  | 0 => ⟨((1085901240573751/1125899906842624), (-34153331086929/1125899906842624)), (529/1125899906842624), by norm_num⟩
  | _ => zero

def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((1085901240573751/1125899906842624), (-34153331086929/1125899906842624)), (2017979148482921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((523143774635705/562949953421312), (-131760005917493/2251799813685248)), (1053/1125899906842624), by norm_num⟩
  | 2 => ⟨((968449730161439/1125899906842624), (-122443258806193/1125899906842624)), (2081/1125899906842624), by norm_num⟩
  | 3 => ⟨((1639404218108147/2251799813685248), (-421281288790513/2251799813685248)), (4033/1125899906842624), by norm_num⟩
  | 4 => ⟨((557369320933929/1125899906842624), (-613420711428961/2251799813685248)), (3691/562949953421312), by norm_num⟩
  | 5 => ⟨((384739915687941/2251799813685248), (-1214679504982881/4503599627370496)), (11331/1125899906842624), by norm_num⟩
  | 6 => ⟨((-196142455373405/4503599627370496), (-415077474911193/4503599627370496)), (79875/9007199254740992), by norm_num⟩
  | _ => zero

def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-19614186453/8589934592), (-138280014493/68719476736)), (1/34359738368), by norm_num⟩, 0, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨1,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 12 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨1,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 12 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨1,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 12 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨1,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 12 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨1,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 12 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨1,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiRectangle.Tile001Terms2
