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
namespace Reinmann.XiRectangle.Tile029Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨29,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5/8), (1551/128)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((5/8), (1551/128))
  have he : value ((5/8), (1551/128))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-372130559/134217728), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-232581599/134217728), (-2254587879/67108864)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-372130559/134217728), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-455591238505099/4503599627370496), (-20402730528239/140737488355328)), (71446451/9007199254740992), by norm_num⟩
  | 1 => ⟨((1204650049/4294967296), (3452659947/8589934592)), (191/8589934592), by norm_num⟩
  | 2 => ⟨((-834999785/2147483648), (-598300377/1073741824)), (267/8589934592), by norm_num⟩
  | 3 => ⟨((3086814649/8589934592), (2211787837/4294967296)), (249/8589934592), by norm_num⟩
  | 4 => ⟨((-2139616871/8589934592), (-3066189007/8589934592)), (87/4294967296), by norm_num⟩
  | 5 => ⟨((2372911043/17179869184), (3400512425/17179869184)), (195/17179869184), by norm_num⟩
  | 6 => ⟨((-1096517733/17179869184), (-49105325/536870912)), (91/17179869184), by norm_num⟩
  | 7 => ⟨((3474505943/137438953472), (4979158685/137438953472)), (291/137438953472), by norm_num⟩
  | 8 => ⟨((-1204171999/137438953472), (-862822451/68719476736)), (51/68719476736), by norm_num⟩
  | 9 => ⟨((2967709959/1099511627776), (1063223021/274877906944)), (127/549755813888), by norm_num⟩
  | 10 => ⟨((-3291295665/4398046511104), (-1179152063/1099511627776)), (71/1099511627776), by norm_num⟩
  | 11 => ⟨((1659165317/8796093022208), (2377675427/8796093022208)), (289/17592186044416), by norm_num⟩
  | 12 => ⟨((-1533394349/35184372088832), (-4394877383/70368744177664)), (269/70368744177664), by norm_num⟩
  | _ => zero

def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790859256563237/5070602400912917605986812821504), (-2839759668341/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779290023017159/633825300114114700748351602688), (-420325427207/79228162514264337593543950336)), (23133/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945163932440487/19807040628566084398385987584), (-59099057365/618970019642690137449562112)), (13015/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1890139067064913/2475880078570760549798248448), (-4018024043223/2475880078570760549798248448)), (27663/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771804757664719/154742504910672534362390528), (-4017223263205/154742504910672534362390528)), (13835/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((775064261343861/4835703278458516698824704), (-941324022081/2417851639229258349412352)), (6487/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1259291300503183/604462909807314587353088), (-3293783477531/604462909807314587353088)), (2839/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((944303842837837/37778931862957161709568), (-2675401767033/37778931862957161709568)), (4615/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((162268776418389/590295810358705651712), (-4011707618479/4722366482869645213696)), (27703/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405571581841025/147573952589676412928), (-2756915765905/295147905179352825856)), (38111/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912260008150659/36893488147419103232), (-3444445298019/36893488147419103232)), (47667/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823829699941113/9223372036854775808), (-3872664960809/4611686018427387904)), (26833/4611686018427387904), by norm_num⟩
  | 6 => ⟨((99692132680745/72057594037927936), (-7739491989895/1152921504606846976)), (53717/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597764202943351/72057594037927936), (-6765490662763/144115188075855872)), (11765/36028797018963968), by norm_num⟩
  | 4 => ⟨((373262427961045/9007199254740992), (-10135113457603/36028797018963968)), (70703/36028797018963968), by norm_num⟩
  | 3 => ⟨((1491007090421235/9007199254740992), (-6322971713131/4503599627370496)), (88579/9007199254740992), by norm_num⟩
  | 2 => ⟨((1115699566224185/2251799813685248), (-12611552975491/2251799813685248)), (88879/2251799813685248), by norm_num⟩
  | 1 => ⟨((555290368086167/562949953421312), (-4707866522265/281474976710656)), (134071/1125899906842624), by norm_num⟩
  | 0 => ⟨((1095188292525599/1125899906842624), (-9330039302301/281474976710656)), (33895/140737488355328), by norm_num⟩
  | _ => zero

def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((1095188292525599/1125899906842624), (-9330039302301/281474976710656)), (129299164355230287/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((66504835080695/70368744177664), (-72604321223109/1125899906842624)), (17047/35184372088832), by norm_num⟩
  | 2 => ⟨((1000967525179423/1125899906842624), (-137235315636663/1125899906842624)), (1101457/1125899906842624), by norm_num⟩
  | 3 => ⟨((218292596133801/281474976710656), (-488029507508427/2251799813685248)), (1113493/562949953421312), by norm_num⟩
  | 4 => ⟨((1248571593456707/2251799813685248), (-756964114031539/2251799813685248)), (8838995/2251799813685248), by norm_num⟩
  | 5 => ⟨((1710326939199/8796093022208), (-839438643081805/2251799813685248)), (15744669/2251799813685248), by norm_num⟩
  | 6 => ⟨((-455591238505099/4503599627370496), (-20402730528239/140737488355328)), (71446451/9007199254740992), by norm_num⟩
  | _ => zero

def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-232581599/134217728), (-2254587879/67108864)), (1/67108864), by norm_num⟩, -5, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-190133729/67108864), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-237667161/134217728), (-4607772089/134217728)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-190133729/67108864), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-373437748972657/2251799813685248), (-344936789188497/9007199254740992)), (8188371/1125899906842624), by norm_num⟩
  | 1 => ⟨((2018029811/4294967296), (233001593/2147483648)), (179/8589934592), by norm_num⟩
  | 2 => ⟨((-2858754495/4294967296), (-1320286445/8589934592)), (1/33554432), by norm_num⟩
  | 3 => ⟨((2699820461/4294967296), (1246884391/8589934592)), (61/2147483648), by norm_num⟩
  | 4 => ⟨((-3824583679/8589934592), (-441586187/4294967296)), (175/8589934592), by norm_num⟩
  | 5 => ⟨((2167172303/8589934592), (500443151/8589934592)), (25/2147483648), by norm_num⟩
  | 6 => ⟨((-4093374325/34359738368), (-236310369/8589934592)), (191/34359738368), by norm_num⟩
  | 7 => ⟨((1656771823/34359738368), (765163075/68719476736)), (39/17179869184), by norm_num⟩
  | 8 => ⟨((-4693988037/274877906944), (-1083935117/274877906944)), (223/274877906944), by norm_num⟩
  | 9 => ⟨((5910697575/1099511627776), (170612191/137438953472)), (283/1099511627776), by norm_num⟩
  | 10 => ⟨((-6698506897/4398046511104), (-386704589/1099511627776)), (323/4398046511104), by norm_num⟩
  | 11 => ⟨((6901199683/17592186044416), (398406037/4398046511104)), (335/17592186044416), by norm_num⟩
  | 12 => ⟨((-3258761839/35184372088832), (-752512867/35184372088832)), (319/70368744177664), by norm_num⟩
  | _ => zero

def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790834578331793/5070602400912917605986812821504), (-3796658070503/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889613410119835/316912650057057350374175801344), (-4495400669785/633825300114114700748351602688)), (23161/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945128249846815/19807040628566084398385987584), (-5056508379775/39614081257132168796771975168)), (1629/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((1890062903830625/2475880078570760549798248448), (-5371566149573/2475880078570760549798248448)), (27701/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221466026839247/19342813113834066795298816), (-2685235147293/77371252455336267181195264)), (13855/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1550056360453543/9671406556917033397649408), (-314603224339/604462909807314587353088)), (6497/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((629613877794929/302231454903657293676544), (-1100820216789/151115727451828646838272)), (22749/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888503670195695/75557863725914323419136), (-1788287119425/18889465931478580854784)), (36985/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298071539666873/4722366482869645213696), (-2681475687673/2361183241434822606848)), (6939/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((25346516909729/9223372036854775808), (-3599098913/288230376151711744)), (19095/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1824381854310179/73786976294838206464), (-9209038139787/73786976294838206464)), (1493/2305843009213693952), by norm_num⟩
  | 7 => ⟨((1823672062986113/9223372036854775808), (-10353767624135/9223372036854775808)), (53803/9223372036854775808), by norm_num⟩
  | 6 => ⟨((797456867222777/576460752303423488), (-10345767950073/1152921504606846976)), (53871/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195384976618897/144115188075855872), (-2260887067367/36028797018963968)), (47213/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492828404306335/36028797018963968), (-13547327431699/36028797018963968)), (17743/9007199254740992), by norm_num⟩
  | 3 => ⟨((1490719703629715/9007199254740992), (-8451336793255/4503599627370496)), (88983/9007199254740992), by norm_num⟩
  | 2 => ⟨((557698059405541/1125899906842624), (-16855456269069/2251799813685248)), (11173/281474976710656), by norm_num⟩
  | 1 => ⟨((555042825504455/562949953421312), (-25165181516013/1125899906842624)), (33771/281474976710656), by norm_num⟩
  | 0 => ⟨((34188746532781/35184372088832), (-24929301247103/562949953421312)), (68553/281474976710656), by norm_num⟩
  | _ => zero

def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((34188746532781/35184372088832), (-24929301247103/562949953421312)), (261508942724132449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((132609190138539/140737488355328), (-96895469320833/1125899906842624)), (69649/140737488355328), by norm_num⟩
  | 2 => ⟨((991263867268305/1125899906842624), (-182598536678275/1125899906842624)), (143241/140737488355328), by norm_num⟩
  | 3 => ⟨((52694616945163/70368744177664), (-321526506086727/1125899906842624)), (149343/70368744177664), by norm_num⟩
  | 4 => ⟨((1079068755350597/2251799813685248), (-120385238318169/281474976710656)), (9886827/2251799813685248), by norm_num⟩
  | 5 => ⟨((105188133784953/2251799813685248), (-461511537517977/1125899906842624)), (35865339/4503599627370496), by norm_num⟩
  | 6 => ⟨((-373437748972657/2251799813685248), (-344936789188497/9007199254740992)), (8188371/1125899906842624), by norm_num⟩
  | _ => zero

def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-237667161/134217728), (-4607772089/134217728)), (1/67108864), by norm_num⟩, -5, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-6207026087/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-242461957/134217728), (-2350365591/67108864)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-6207026087/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-660878988937693/4503599627370496), (664202816600281/9007199254740992)), (32949865/4503599627370496), by norm_num⟩
  | 1 => ⟨((3643390589/8589934592), (-1830857337/8589934592)), (183/8589934592), by norm_num⟩
  | 2 => ⟨((-5265376631/8589934592), (1322964585/4294967296)), (133/4294967296), by norm_num⟩
  | 3 => ⟨((5072965303/8589934592), (-2549239649/8589934592)), (129/4294967296), by norm_num⟩
  | 4 => ⟨((-1832844455/4294967296), (1842062571/8589934592)), (189/8589934592), by norm_num⟩
  | 5 => ⟨((529760185/2147483648), (-2129698253/17179869184)), (221/17179869184), by norm_num⟩
  | 6 => ⟨((-4083210339/34359738368), (512968307/8589934592)), (215/34359738368), by norm_num⟩
  | 7 => ⟨((3371998813/68719476736), (-423619745/17179869184)), (179/68719476736), by norm_num⟩
  | 8 => ⟨((-4873165069/274877906944), (1224418547/137438953472)), (261/274877906944), by norm_num⟩
  | 9 => ⟨((1565028743/274877906944), (-786449953/274877906944)), (169/549755813888), by norm_num⟩
  | 10 => ⟨((-3618811903/2199023255552), (1818506187/2199023255552)), (99/1099511627776), by norm_num⟩
  | 11 => ⟨((3803531535/8796093022208), (-955665259/4398046511104)), (105/4398046511104), by norm_num⟩
  | 12 => ⟨((-3664540043/35184372088832), (920742625/17592186044416)), (51/8796093022208), by norm_num⟩
  | _ => zero

def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581622622146687/10141204801825835211973625643008), (3485704507245/10141204801825835211973625643008)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((222396677591639/79228162514264337593543950336), (2063487770241/316912650057057350374175801344)), (23153/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890196533233557/39614081257132168796771975168), (4642087563999/39614081257132168796771975168)), (26053/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889999326495391/2475880078570760549798248448), (4931306436915/2475880078570760549798248448)), (3461/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((442916197867973/38685626227668133590597632), (4930280869275/154742504910672534362390528)), (27697/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774998532405557/4835703278458516698824704), (2310524366449/4835703278458516698824704)), (25975/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259176035463335/604462909807314587353088), (4042328152993/604462909807314587353088)), (22737/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888419931482573/75557863725914323419136), (6566740657611/75557863725914323419136)), (36965/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649004501814649/2361183241434822606848), (4923268425977/4722366482869645213696)), (27739/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202761441290275/73786976294838206464), (6766590477023/590295810358705651712)), (9541/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1824275566558819/73786976294838206464), (8453883341947/73786976294838206464)), (47741/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455888346239347/2305843009213693952), (4752316022845/4611686018427387904)), (53759/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594796174562431/1152921504606846976), (9497150267887/1152921504606846976)), (53821/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195283367615321/144115188075855872), (4150795856255/72057594037927936)), (47163/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492678497540231/36028797018963968), (12435563619073/36028797018963968)), (70885/36028797018963968), by norm_num⟩
  | 3 => ⟨((1490536695605631/9007199254740992), (15515025263743/9007199254740992)), (22213/2251799813685248), by norm_num⟩
  | 2 => ⟨((69701228201105/140737488355328), (1933863354973/281474976710656)), (22305/562949953421312), by norm_num⟩
  | 1 => ⟨((138729652647587/140737488355328), (23096154060155/1125899906842624)), (134755/1125899906842624), by norm_num⟩
  | 0 => ⟨((1093607638590829/1125899906842624), (45752028290471/1125899906842624)), (68305/281474976710656), by norm_num⟩
  | _ => zero

def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((1093607638590829/1125899906842624), (45752028290471/1125899906842624)), (260562897802257449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((530191188326653/562949953421312), (44439800834335/562949953421312)), (276487/562949953421312), by norm_num⟩
  | 2 => ⟨((61978822136995/70368744177664), (167415171953819/1125899906842624)), (1128897/1125899906842624), by norm_num⟩
  | 3 => ⟨((848533692139707/1125899906842624), (147454601994357/562949953421312)), (581081/281474976710656), by norm_num⟩
  | 4 => ⟨((17570333746247/35184372088832), (889032476815023/2251799813685248)), (9442161/2251799813685248), by norm_num⟩
  | 5 => ⟨((421107205345985/4503599627370496), (443964078411129/1125899906842624)), (16886147/2251799813685248), by norm_num⟩
  | 6 => ⟨((-660878988937693/4503599627370496), (664202816600281/9007199254740992)), (32949865/4503599627370496), by norm_num⟩
  | _ => zero

def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-242461957/134217728), (-2350365591/67108864)), (1/67108864), by norm_num⟩, -6, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-197597955/67108864), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-61749361/33554432), (-4788662941/134217728)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-197597955/67108864), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-155510714629807/2251799813685248), (1287738692547469/9007199254740992)), (63180769/9007199254740992), by norm_num⟩
  | 1 => ⟨((1746718635/8589934592), (-3616016389/8589934592)), (179/8589934592), by norm_num⟩
  | 2 => ⟨((-2571553217/8589934592), (2661784901/4294967296)), (133/4294967296), by norm_num⟩
  | 3 => ⟨((315490897/1073741824), (-2612487739/4294967296)), (33/1073741824), by norm_num⟩
  | 4 => ⟨((-1857887389/8589934592), (3846155365/8589934592)), (197/8589934592), by norm_num⟩
  | 5 => ⟨((2188174419/17179869184), (-2264953955/8589934592)), (117/8589934592), by norm_num⟩
  | 6 => ⟨((-536912171/8589934592), (2223006237/17179869184)), (231/34359738368), by norm_num⟩
  | 7 => ⟨((903374357/34359738368), (-1870144633/34359738368)), (49/17179869184), by norm_num⟩
  | 8 => ⟨((-2659930669/274877906944), (2753263377/137438953472)), (291/274877906944), by norm_num⟩
  | 9 => ⟨((108777827/34359738368), (-450378667/68719476736)), (3/8589934592), by norm_num⟩
  | 10 => ⟨((-2049853913/2199023255552), (530445001/274877906944)), (57/549755813888), by norm_num⟩
  | 11 => ⟨((2194789005/8796093022208), (-567950159/1099511627776)), (123/4398046511104), by norm_num⟩
  | 12 => ⟨((-1077070383/17592186044416), (2229726115/17592186044416)), (243/35184372088832), by norm_num⟩
  | _ => zero

def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581578604278889/10141204801825835211973625643008), (2632308048847/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222390652563101/79228162514264337593543950336), (3116404540389/633825300114114700748351602688)), (23127/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890142541793351/39614081257132168796771975168), (3505379032255/39614081257132168796771975168)), (3253/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1889942260184861/2475880078570760549798248448), (3723764937585/2475880078570760549798248448)), (27655/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885804031008893/77371252455336267181195264), (930744306275/38685626227668133590597632)), (13831/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549944238667071/9671406556917033397649408), (872363586487/2417851639229258349412352)), (6485/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1259130170092065/604462909807314587353088), (3052435909665/604462909807314587353088)), (1419/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((1888346070120169/75557863725914323419136), (1239659996645/18889465931478580854784)), (36907/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((81122137080297/295147905179352825856), (3717608008259/4722366482869645213696)), (6923/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((811008558485165/295147905179352825856), (5109482177083/590295810358705651712)), (19047/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1824183974683377/73786976294838206464), (6383510583057/73786976294838206464)), (11911/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1823452300791407/9223372036854775808), (1794213943741/2305843009213693952)), (53637/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398674383156637/288230376151711744), (7171116450665/1152921504606846976)), (13421/288230376151711744), by norm_num⟩
  | 5 => ⟨((597599899215821/72057594037927936), (48970889749/1125899906842624)), (23513/72057594037927936), by norm_num⟩
  | 4 => ⟨((1492558616296341/36028797018963968), (9389514155463/36028797018963968)), (70645/36028797018963968), by norm_num⟩
  | 3 => ⟨((1490396392902811/9007199254740992), (5857172263285/4503599627370496)), (22123/2251799813685248), by norm_num⟩
  | 2 => ⟨((1115093615690247/2251799813685248), (11680564327849/2251799813685248)), (44385/1125899906842624), by norm_num⟩
  | 1 => ⟨((277420909928077/281474976710656), (4359135818705/281474976710656)), (133853/1125899906842624), by norm_num⟩
  | 0 => ⟨((136680148526173/140737488355328), (34536758109243/1125899906842624)), (33813/140737488355328), by norm_num⟩
  | _ => zero

def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((136680148526173/140737488355328), (34536758109243/1125899906842624)), (128986359179449037/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((1060858818046787/1125899906842624), (33541093301777/562949953421312)), (67751/140737488355328), by norm_num⟩
  | 2 => ⟨((1991156416757377/2251799813685248), (252827906849405/2251799813685248)), (2171963/2251799813685248), by norm_num⟩
  | 3 => ⟨((866147581549065/1125899906842624), (447126699273185/2251799813685248)), (2164425/1125899906842624), by norm_num⟩
  | 4 => ⟨((621930117825685/1125899906842624), (687943407522847/2251799813685248)), (8379423/2251799813685248), by norm_num⟩
  | 5 => ⟨((119229310189321/562949953421312), (760019113418209/2251799813685248)), (3594325/562949953421312), by norm_num⟩
  | 6 => ⟨((-155510714629807/2251799813685248), (1287738692547469/9007199254740992)), (63180769/9007199254740992), by norm_num⟩
  | _ => zero

def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-61749361/33554432), (-4788662941/134217728)), (1/67108864), by norm_num⟩, -6, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-6433286071/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-251300237/134217728), (-1218020837/33554432)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-6433286071/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((236409394200059/9007199254740992), (1364662035871885/9007199254740992)), (52483783/9007199254740992), by norm_num⟩
  | 1 => ⟨((-675410511/8589934592), (-3898775199/8589934592)), (151/8589934592), by norm_num⟩
  | 2 => ⟨((1011674533/8589934592), (5839843345/8589934592)), (57/2147483648), by norm_num⟩
  | 3 => ⟨((-505117675/4294967296), (-5831535727/8589934592)), (115/4294967296), by norm_num⟩
  | 4 => ⟨((189149665/2147483648), (4367429945/8589934592)), (87/4294967296), by norm_num⟩
  | 5 => ⟨((-453313405/8589934592), (-5233460335/17179869184)), (211/17179869184), by norm_num⟩
  | 6 => ⟨((905337065/34359738368), (2613007671/17179869184)), (213/34359738368), by norm_num⟩
  | 7 => ⟨((-774899275/68719476736), (-2236534689/34359738368)), (23/8589934592), by norm_num⟩
  | 8 => ⟨((1160695383/274877906944), (6700059149/274877906944)), (139/137438953472), by norm_num⟩
  | 9 => ⟨((-772696137/549755813888), (-4460351873/549755813888)), (187/549755813888), by norm_num⟩
  | 10 => ⟨((462958151/1099511627776), (5344808023/2199023255552)), (113/1099511627776), by norm_num⟩
  | 11 => ⟨((-1008653581/8796093022208), (-5822405051/8796093022208)), (31/1099511627776), by norm_num⟩
  | 12 => ⟨((1007218695/35184372088832), (22711415/137438953472)), (249/35184372088832), by norm_num⟩
  | _ => zero

def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790768422377973/5070602400912917605986812821504), (1822695222929/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779078486498029/633825300114114700748351602688), (2157785163531/633825300114114700748351602688)), (361/9903520314283042199192993792), by norm_num⟩
  | 16 => ⟨((1890090129743563/39614081257132168796771975168), (606776649571/9903520314283042199192993792)), (25995/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889886782499739/2475880078570760549798248448), (644576975509/618970019642690137449562112)), (3453/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1771552820566009/154742504910672534362390528), (1288876785369/77371252455336267181195264)), (6907/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((774946350333957/4835703278458516698824704), (2416055133131/9671406556917033397649408)), (12953/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((39346416407865/18889465931478580854784), (2113459556785/604462909807314587353088)), (22673/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888273666683673/75557863725914323419136), (3433268324687/75557863725914323419136)), (9213/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1297900301417369/4722366482869645213696), (1286993024485/2361183241434822606848)), (27647/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810971841223787/295147905179352825856), (3537662992265/590295810358705651712)), (19013/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1824093180657407/73786976294838206464), (4419728080519/73786976294838206464)), (743/1152921504606846976), by norm_num⟩
  | 7 => ⟨((1823351529583183/9223372036854775808), (621120460517/1152921504606846976)), (26761/4611686018427387904), by norm_num⟩
  | 6 => ⟨((797299236957553/576460752303423488), (4964928301195/1152921504606846976)), (26777/576460752303423488), by norm_num⟩
  | 5 => ⟨((1195115045057263/144115188075855872), (2169888032763/72057594037927936)), (46897/144115188075855872), by norm_num⟩
  | 4 => ⟨((373108830834691/9007199254740992), (3250300358241/18014398509481984)), (35209/18014398509481984), by norm_num⟩
  | 3 => ⟨((1490248971656581/9007199254740992), (8109910245037/9007199254740992)), (44075/4503599627370496), by norm_num⟩
  | 2 => ⟨((557478098486779/1125899906842624), (16172379536671/4503599627370496)), (88343/2251799813685248), by norm_num⟩
  | 1 => ⟨((2219004757239343/2251799813685248), (12070125045489/1125899906842624)), (66499/562949953421312), by norm_num⟩
  | 0 => ⟨((2186354600552899/2251799813685248), (47808919745891/2251799813685248)), (535871/2251799813685248), by norm_num⟩
  | _ => zero

def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((2186354600552899/2251799813685248), (47808919745891/2251799813685248)), (2044185647017668967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2121796403709711/2251799813685248), (92838849171789/2251799813685248)), (1063349/2251799813685248), by norm_num⟩
  | 2 => ⟨((1995470867157643/2251799813685248), (174957947060905/2251799813685248)), (2091599/2251799813685248), by norm_num⟩
  | 3 => ⟨((1754726896423579/2251799813685248), (310083946375657/2251799813685248)), (4032035/2251799813685248), by norm_num⟩
  | 4 => ⟨((1324680111039999/2251799813685248), (30204319093315/140737488355328)), (57769/17592186044416), by norm_num⟩
  | 5 => ⟨((168890276015621/562949953421312), (284295685804779/1125899906842624)), (11873843/2251799813685248), by norm_num⟩
  | 6 => ⟨((236409394200059/9007199254740992), (1364662035871885/9007199254740992)), (52483783/9007199254740992), by norm_num⟩
  | _ => zero

def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-251300237/134217728), (-1218020837/33554432)), (1/67108864), by norm_num⟩, -6, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-6538062151/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-255393053/134217728), (-4951432811/134217728)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-6538062151/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((464074958537961/4503599627370496), (242801282249951/2251799813685248)), (19303723/4503599627370496), by norm_num⟩
  | 1 => ⟨((-2694867371/8589934592), (-44060585/134217728)), (57/4294967296), by norm_num⟩
  | 2 => ⟨((4102292089/8589934592), (4292590069/8589934592)), (11/536870912), by norm_num⟩
  | 3 => ⟨((-4163173437/8589934592), (-2178147797/4294967296)), (181/8589934592), by norm_num⟩
  | 4 => ⟨((3168718735/8589934592), (103615935/268435456)), (35/2147483648), by norm_num⟩
  | 5 => ⟨((-3858894115/17179869184), (-4037901299/17179869184)), (173/17179869184), by norm_num⟩
  | 6 => ⟨((3916163239/34359738368), (4097827035/34359738368)), (89/17179869184), by norm_num⟩
  | 7 => ⟨((-425815959/8589934592), (-3564550387/68719476736)), (157/68719476736), by norm_num⟩
  | 8 => ⟨((2592812483/137438953472), (339136051/17179869184)), (121/137438953472), by norm_num⟩
  | 9 => ⟨((-877097309/137438953472), (-1835568563/274877906944)), (83/274877906944), by norm_num⟩
  | 10 => ⟨((1068136975/549755813888), (1117685935/549755813888)), (103/1099511627776), by norm_num⟩
  | 11 => ⟨((-591266725/1099511627776), (-2474778115/4398046511104)), (29/1099511627776), by norm_num⟩
  | 12 => ⟨((2400166415/17592186044416), (2511505833/17592186044416)), (15/2199023255552), by norm_num⟩
  | _ => zero

def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581497123104531/10141204801825835211973625643008), (1052591776005/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779033123505717/633825300114114700748351602688), (311510205205/158456325028528675187087900672)), (11541/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890039199844963/39614081257132168796771975168), (350390419307/9903520314283042199192993792)), (25969/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944916401203187/1237940039285380274899124224), (372217550913/618970019642690137449562112)), (13797/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771498989910479/154742504910672534362390528), (744272545657/77371252455336267181195264)), (6899/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1549842393119255/9671406556917033397649408), (697582842887/4835703278458516698824704)), (12937/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629520732269917/302231454903657293676544), (1220424744067/604462909807314587353088)), (22643/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888202690506791/75557863725914323419136), (1982543126925/75557863725914323419136)), (36799/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297847329087889/4722366482869645213696), (743170687055/2361183241434822606848)), (6901/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((405467816821553/147573952589676412928), (2042800109633/590295810358705651712)), (37963/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824003293713839/73786976294838206464), (2552121957697/73786976294838206464)), (5933/9223372036854775808), by norm_num⟩
  | 7 => ⟨((911625637339891/4611686018427387904), (11207982063/36028797018963968)), (13353/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1594499302243837/1152921504606846976), (2866877967553/1152921504606846976)), (53431/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597514743105381/72057594037927936), (1252929788573/72057594037927936)), (46773/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492309412132805/36028797018963968), (1876739130709/18014398509481984)), (35101/18014398509481984), by norm_num⟩
  | 3 => ⟨((1490095817279325/9007199254740992), (1170641823405/2251799813685248)), (87827/9007199254740992), by norm_num⟩
  | 2 => ⟨((2229618738264279/4503599627370496), (9337348505213/4503599627370496)), (43969/1125899906842624), by norm_num⟩
  | 1 => ⟨((1109297864504125/1125899906842624), (13936751503901/2251799813685248)), (264375/2251799813685248), by norm_num⟩
  | 0 => ⟨((1092830652390537/1125899906842624), (13798789412455/1125899906842624)), (531001/2251799813685248), by norm_num⟩
  | _ => zero

def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((1092830652390537/1125899906842624), (13798789412455/1125899906842624)), (2025608071334075217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((530281786577137/562949953421312), (13393499674497/562949953421312)), (521913/1125899906842624), by norm_num⟩
  | 2 => ⟨((1996762842835477/2251799813685248), (100930164647829/2251799813685248)), (2016175/2251799813685248), by norm_num⟩
  | 3 => ⟨((1766087255280525/2251799813685248), (178997796576087/2251799813685248)), (3756389/2251799813685248), by norm_num⟩
  | 4 => ⟨((342728510248103/562949953421312), (140388024430537/1125899906842624)), (6489473/2251799813685248), by norm_num⟩
  | 5 => ⟨((399806880530231/1125899906842624), (341877484329361/2251799813685248)), (9520029/2251799813685248), by norm_num⟩
  | 6 => ⟨((464074958537961/4503599627370496), (242801282249951/2251799813685248)), (19303723/4503599627370496), by norm_num⟩
  | _ => zero

def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-255393053/134217728), (-4951432811/134217728)), (1/67108864), by norm_num⟩, -6, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨29,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 12 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨29,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 12 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨29,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 12 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨29,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 12 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨29,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 12 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨29,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiRectangle.Tile029Terms2
