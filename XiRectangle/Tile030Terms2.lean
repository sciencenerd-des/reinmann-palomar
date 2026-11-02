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
namespace Reinmann.XiRectangle.Tile030Terms2
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
  | 0 => ⟨((-325614239/134217728), (-2254587879/67108864)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((-455591237637383/9007199254740992), (-652887375660127/9007199254740992)), (72232727/18014398509481984), by norm_num⟩
  | 1 => ⟨((1204650047/8589934592), (863164985/4294967296)), (193/17179869184), by norm_num⟩
  | 2 => ⟨((-3339999135/17179869184), (-2393201503/8589934592)), (135/8589934592), by norm_num⟩
  | 3 => ⟨((3086814645/17179869184), (4423575665/17179869184)), (63/4294967296), by norm_num⟩
  | 4 => ⟨((-534904217/4294967296), (-383273625/2147483648)), (177/17179869184), by norm_num⟩
  | 5 => ⟨((2372911039/34359738368), (3400512417/34359738368)), (99/17179869184), by norm_num⟩
  | 6 => ⟨((-1096517731/34359738368), (-3142740793/68719476736)), (185/68719476736), by norm_num⟩
  | 7 => ⟨((3474505937/274877906944), (2489579337/137438953472)), (295/274877906944), by norm_num⟩
  | 8 => ⟨((-1204171997/274877906944), (-3451289797/549755813888)), (207/549755813888), by norm_num⟩
  | 9 => ⟨((1483854977/1099511627776), (4252892075/2199023255552)), (257/2199023255552), by norm_num⟩
  | 10 => ⟨((-822823915/2199023255552), (-2358304121/4398046511104)), (287/8796093022208), by norm_num⟩
  | 11 => ⟨((3318330629/35184372088832), (1188837711/8796093022208)), (73/8796093022208), by norm_num⟩
  | 12 => ⟨((-3066788693/140737488355328), (-2197438687/70368744177664)), (17/8796093022208), by norm_num⟩
  | _ => zero

def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580815611531029/10141204801825835211973625643008), (-2839759668341/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778221494425467/633825300114114700748351602688), (-104961216945/19807040628566084398385987584)), (23133/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944563000204863/19807040628566084398385987584), (-3777797777785/39614081257132168796771975168)), (13015/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((118053897392819/154742504910672534362390528), (-2006457907805/1237940039285380274899124224)), (1729/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((1770528355205941/154742504910672534362390528), (-4011797501975/154742504910672534362390528)), (13835/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774466110428071/4835703278458516698824704), (-1879936136787/4835703278458516698824704)), (6487/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((629122430941327/302231454903657293676544), (-3288700718769/604462909807314587353088)), (2839/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((117931739575891/4722366482869645213696), (-2670956420043/37778931862957161709568)), (36921/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296875856028607/4722366482869645213696), (-4004487803751/4722366482869645213696)), (27703/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620534956628627/590295810358705651712), (-1375752146683/147573952589676412928)), (38111/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822332104679271/73786976294838206464), (-214813126691/2305843009213693952)), (11917/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1821370089426639/9223372036854775808), (-965844780829/1152921504606846976)), (53667/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592616750082763/1152921504606846976), (-1929655382971/288230376151711744)), (53717/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193380722269853/144115188075855872), (-6744648528463/144115188075855872)), (11765/36028797018963968), by norm_num⟩
  | 4 => ⟨((372458305503787/9007199254740992), (-10098703391175/36028797018963968)), (4419/2251799813685248), by norm_num⟩
  | 3 => ⟨((1486995291310873/9007199254740992), (-1573931939303/1125899906842624)), (88581/9007199254740992), by norm_num⟩
  | 2 => ⟨((2223401977042155/4503599627370496), (-25087330656319/4503599627370496)), (44441/1125899906842624), by norm_num⟩
  | 1 => ⟨((2209231856684209/2251799813685248), (-1168522261049/70368744177664)), (268157/2251799813685248), by norm_num⟩
  | 0 => ⟨((1083390938656159/1125899906842624), (-73836289934099/2251799813685248)), (542383/2251799813685248), by norm_num⟩
  | _ => zero

def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((1083390938656159/1125899906842624), (-73836289934099/2251799813685248)), (2069026955611418967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2082552755195027/2251799813685248), (-142097120663095/2251799813685248)), (269845/562949953421312), by norm_num⟩
  | 2 => ⟨((1917059571740889/2251799813685248), (-262833976931461/2251799813685248)), (2132733/2251799813685248), by norm_num⟩
  | 3 => ⟨((800700772834729/1125899906842624), (-447525031481871/2251799813685248)), (4129259/2251799813685248), by norm_num⟩
  | 4 => ⟨((131239922078179/281474976710656), (-39783025603859/140737488355328)), (7514477/2251799813685248), by norm_num⟩
  | 5 => ⟨((619204493108173/4503599627370496), (-296786378173957/1125899906842624)), (2813921/562949953421312), by norm_num⟩
  | 6 => ⟨((-455591237637383/9007199254740992), (-652887375660127/9007199254740992)), (72232727/18014398509481984), by norm_num⟩
  | _ => zero

def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-325614239/134217728), (-2254587879/67108864)), (1/67108864), by norm_num⟩, -5, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-166367013/67108864), (-4607772089/134217728)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((-1471282168630751/18014398509481984), (-42468536308425/2251799813685248)), (65247877/18014398509481984), by norm_num⟩
  | 1 => ⟨((3975349687/17179869184), (458993621/8589934592)), (89/8589934592), by norm_num⟩
  | 2 => ⟨((-5631506891/17179869184), (-325106713/4294967296)), (127/8589934592), by norm_num⟩
  | 3 => ⟨((5318420157/17179869184), (1228128903/17179869184)), (121/8589934592), by norm_num⟩
  | 4 => ⟨((-941763685/4294967296), (-869887799/17179869184)), (173/17179869184), by norm_num⟩
  | 5 => ⟨((4269147903/34359738368), (61614443/2147483648)), (99/17179869184), by norm_num⟩
  | 6 => ⟨((-4031802269/68719476736), (-931023265/68719476736)), (189/68719476736), by norm_num⟩
  | 7 => ⟨((6527403423/274877906944), (1507307165/274877906944)), (77/68719476736), by norm_num⟩
  | 8 => ⟨((-1155845405/137438953472), (-1067630693/549755813888)), (55/137438953472), by norm_num⟩
  | 9 => ⟨((1455447389/549755813888), (336091725/549755813888)), (279/2199023255552), by norm_num⟩
  | 10 => ⟨((-6597748743/8796093022208), (-23805489/137438953472)), (159/4398046511104), by norm_num⟩
  | 11 => ⟨((6797392647/35184372088832), (1569653041/35184372088832)), (165/17592186044416), by norm_num⟩
  | 12 => ⟨((-6419487851/140737488355328), (-741193657/70368744177664)), (157/70368744177664), by norm_num⟩
  | _ => zero

def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580746512481045/10141204801825835211973625643008), (-3796658070503/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778135009444499/633825300114114700748351602688), (-4490148354177/633825300114114700748351602688)), (23161/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236128557783477/4951760157141521099596496896), (-1262575988087/9903520314283042199192993792)), (1629/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((1888758399409227/2475880078570760549798248448), (-2682294080225/1237940039285380274899124224)), (27701/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885212015764285/77371252455336267181195264), (-5363058601017/154742504910672534362390528)), (13855/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774417015061435/4835703278458516698824704), (-1256560654547/2417851639229258349412352)), (6497/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((314539639515113/151115727451828646838272), (-4396337848607/604462909807314587353088)), (11375/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943383432381313/37778931862957161709568), (-7141003978107/75557863725914323419136)), (18493/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648384748147881/2361183241434822606848), (-5353089389689/4722366482869645213696)), (6939/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1620387684143067/590295810358705651712), (-3678085539223/295147905179352825856)), (19095/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822146474763071/73786976294838206464), (-9188726239273/73786976294838206464)), (47777/73786976294838206464), by norm_num⟩
  | 7 => ⟨((113822446451943/576460752303423488), (-10328400849195/9223372036854775808)), (53803/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592403169221881/1152921504606846976), (-10317262079125/1152921504606846976)), (53871/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193190883271099/144115188075855872), (-9015082068139/144115188075855872)), (23607/72057594037927936), by norm_num⟩
  | 4 => ⟨((1489542572628645/36028797018963968), (-3374400195939/9007199254740992)), (70973/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486621716796585/9007199254740992), (-16828261892299/9007199254740992)), (88985/9007199254740992), by norm_num⟩
  | 2 => ⟨((1111312112176169/2251799813685248), (-4190688335319/562949953421312)), (22347/562949953421312), by norm_num⟩
  | 1 => ⟨((551997340757861/562949953421312), (-12490354770353/562949953421312)), (135093/1125899906842624), by norm_num⟩
  | 0 => ⟨((1081998641961331/1125899906842624), (-49309847592225/1125899906842624)), (274247/1125899906842624), by norm_num⟩
  | _ => zero

def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((1081998641961331/1125899906842624), (-49309847592225/1125899906842624)), (1046169285300826671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1037649610801413/1125899906842624), (-94774300638725/1125899906842624)), (551129/1125899906842624), by norm_num⟩
  | 2 => ⟨((1896677564756225/2251799813685248), (-349382802411033/2251799813685248)), (2217291/2251799813685248), by norm_num⟩
  | 3 => ⟨((1543350976808807/2251799813685248), (-294283052524175/1125899906842624)), (276455/140737488355328), by norm_num⟩
  | 4 => ⟨((903953435484845/2251799813685248), (-806789366996453/2251799813685248)), (4187791/1125899906842624), by norm_num⟩
  | 5 => ⟨((147635442383557/4503599627370496), (-1295497078517881/4503599627370496)), (25452471/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1471282168630751/18014398509481984), (-42468536308425/2251799813685248)), (65247877/18014398509481984), by norm_num⟩
  | _ => zero

def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-166367013/67108864), (-4607772089/134217728)), (1/67108864), by norm_num⟩, -5, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-339446739/134217728), (-2350365591/67108864)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((-1283405250679553/18014398509481984), (644930007315901/18014398509481984)), (32361337/9007199254740992), by norm_num⟩
  | 1 => ⟨((27638065/134217728), (-6944267/67108864)), (45/4294967296), by norm_num⟩
  | 2 => ⟨((-5112594081/17179869184), (642288423/4294967296)), (263/17179869184), by norm_num⟩
  | 3 => ⟨((4925765847/17179869184), (-1237634879/8589934592)), (1/67108864), by norm_num⟩
  | 4 => ⟨((-3559323623/17179869184), (1788612451/17179869184)), (187/17179869184), by norm_num⟩
  | 5 => ⟨((4115107391/34359738368), (-1033950983/17179869184)), (109/17179869184), by norm_num⟩
  | 6 => ⟨((-3964730061/68719476736), (1992335147/68719476736)), (53/17179869184), by norm_num⟩
  | 7 => ⟨((1637077685/68719476736), (-411327803/34359738368)), (177/137438953472), by norm_num⟩
  | 8 => ⟨((-2365881553/274877906944), (1188890265/274877906944)), (129/274877906944), by norm_num⟩
  | 9 => ⟨((1519617161/549755813888), (-1527259931/1099511627776)), (21/137438953472), by norm_num⟩
  | 10 => ⟨((-878451705/1099511627776), (1765739589/4398046511104)), (49/1099511627776), by norm_num⟩
  | 11 => ⟨((230822909/1099511627776), (-1855870487/17592186044416)), (13/1099511627776), by norm_num⟩
  | 12 => ⟨((-889552023/17592186044416), (1788051881/70368744177664)), (101/35184372088832), by norm_num⟩
  | _ => zero

def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790340682085487/5070602400912917605986812821504), (3485704507245/10141204801825835211973625643008)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((222257457764947/79228162514264337593543950336), (4122056115775/633825300114114700748351602688)), (1447/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((118058988148847/2475880078570760549798248448), (4636276990005/39614081257132168796771975168)), (26053/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888668604931441/2475880078570760549798248448), (1231192856883/618970019642690137449562112)), (27689/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885167201801311/77371252455336267181195264), (2461669866045/77371252455336267181195264)), (27697/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774375090395631/4835703278458516698824704), (4614110194483/9671406556917033397649408)), (25975/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258085366618013/604462909807314587353088), (4035826033801/604462909807314587353088)), (11369/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886648259755559/75557863725914323419136), (3277683734385/37778931862957161709568)), (36965/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162085103996675/590295810358705651712), (614254110415/590295810358705651712)), (13869/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((405066560131469/147573952589676412928), (6752746213299/590295810358705651712)), (38165/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910997687050885/36893488147419103232), (4217431090213/36893488147419103232)), (23871/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820990121367475/9223372036854775808), (1185109704459/1152921504606846976)), (53759/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592235353193995/1152921504606846976), (2367614212081/288230376151711744)), (53821/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193045397872063/144115188075855872), (4137468066867/72057594037927936)), (11791/36028797018963968), by norm_num⟩
  | 4 => ⟨((372331761109525/9007199254740992), (6194500716163/18014398509481984)), (35443/18014398509481984), by norm_num⟩
  | 3 => ⟨((371589253723789/2251799813685248), (7722675985731/4503599627370496)), (44427/4503599627370496), by norm_num⟩
  | 2 => ⟨((555527219911309/1125899906842624), (7692056166327/1125899906842624)), (11153/281474976710656), by norm_num⟩
  | 1 => ⟨((551812815859045/562949953421312), (22923454885385/1125899906842624)), (33691/281474976710656), by norm_num⟩
  | 0 => ⟨((67583105511767/70368744177664), (5654796192383/140737488355328)), (273257/1125899906842624), by norm_num⟩
  | _ => zero

def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((67583105511767/70368744177664), (5654796192383/140737488355328)), (1042392735007857921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2073412347554169/2251799813685248), (173790198331225/2251799813685248)), (1093677/2251799813685248), by norm_num⟩
  | 2 => ⟨((118483992893439/140737488355328), (320045095406707/2251799813685248)), (2182889/2251799813685248), by norm_num⟩
  | 3 => ⟨((1550500181282587/2251799813685248), (16839960896741/70368744177664)), (4295961/2251799813685248), by norm_num⟩
  | 4 => ⟨((117331728020169/281474976710656), (371050566957203/1125899906842624)), (7972193/2251799813685248), by norm_num⟩
  | 5 => ⟨((293415877066823/4503599627370496), (309341915311393/1125899906842624)), (23801945/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1283405250679553/18014398509481984), (644930007315901/18014398509481984)), (32361337/9007199254740992), by norm_num⟩
  | _ => zero

def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-339446739/134217728), (-2350365591/67108864)), (1/67108864), by norm_num⟩, -6, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-345796421/134217728), (-4788662941/134217728)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((-148971062123185/4503599627370496), (1233585745024485/18014398509481984)), (30616021/9007199254740992), by norm_num⟩
  | 1 => ⟨((1673264321/17179869184), (-865988243/4294967296)), (87/8589934592), by norm_num⟩
  | 2 => ⟨((-307926543/2147483648), (1274924769/4294967296)), (129/8589934592), by norm_num⟩
  | 3 => ⟨((2417789109/17179869184), (-2502625457/8589934592)), (255/17179869184), by norm_num⟩
  | 4 => ⟨((-444939531/4294967296), (3684413973/17179869184)), (189/17179869184), by norm_num⟩
  | 5 => ⟨((2096155677/34359738368), (-4339412847/34359738368)), (225/34359738368), by norm_num⟩
  | 6 => ⟨((-128583385/4294967296), (1064761361/17179869184)), (223/68719476736), by norm_num⟩
  | 7 => ⟨((865384985/68719476736), (-1791499917/68719476736)), (189/137438953472), by norm_num⟩
  | 8 => ⟨((-1274036641/274877906944), (5274962187/549755813888)), (281/549755813888), by norm_num⟩
  | 9 => ⟨((416813683/274877906944), (-3451512061/1099511627776)), (93/549755813888), by norm_num⟩
  | 10 => ⟨((-245456491/549755813888), (1016276665/1099511627776)), (221/4398046511104), by norm_num⟩
  | 11 => ⟨((2102492101/17592186044416), (-4352530365/17592186044416)), (119/8796093022208), by norm_num⟩
  | 12 => ⟨((-128972077/4398046511104), (4271920021/70368744177664)), (59/17592186044416), by norm_num⟩
  | _ => zero

def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580619739154115/10141204801825835211973625643008), (2632308048847/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888995351945787/316912650057057350374175801344), (3112620033365/633825300114114700748351602688)), (23127/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472216616696615/9903520314283042199192993792), (875227353711/9903520314283042199192993792)), (26023/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888586737093631/2475880078570760549798248448), (232421129449/154742504910672534362390528)), (27655/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770252883891507/154742504910672534362390528), (3717637987205/154742504910672534362390528)), (13831/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548674125675991/9671406556917033397649408), (3484117140997/9671406556917033397649408)), (6485/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258019187701603/604462909807314587353088), (190464652457/37778931862957161709568)), (22705/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886541410825001/75557863725914323419136), (2474945865217/37778931862957161709568)), (18453/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648300649980891/2361183241434822606848), (3710504095595/4722366482869645213696)), (6923/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1620157865414269/590295810358705651712), (159338543257/18446744073709551616)), (19047/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821861375201415/73786976294838206464), (3184439992603/36893488147419103232)), (11911/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1820841390401939/9223372036854775808), (1789646188739/2305843009213693952)), (53637/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796044569661955/576460752303423488), (7150585222531/1152921504606846976)), (13421/288230376151711744), by norm_num⟩
  | 5 => ⟨((1192920285393815/144115188075855872), (3123886109603/72057594037927936)), (47027/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489145007377097/36028797018963968), (9353702669187/36028797018963968)), (35323/18014398509481984), by norm_num⟩
  | 3 => ⟨((1486139284304493/9007199254740992), (5830379988867/4503599627370496)), (44247/4503599627370496), by norm_num⟩
  | 2 => ⟨((277712838421949/562949953421312), (11613815411833/2251799813685248)), (88773/2251799813685248), by norm_num⟩
  | 1 => ⟨((275839334360573/281474976710656), (17303739070065/1125899906842624)), (133861/1125899906842624), by norm_num⟩
  | 0 => ⟨((2161873576972367/2251799813685248), (68283603723515/2251799813685248)), (67635/281474976710656), by norm_num⟩
  | _ => zero

def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((2161873576972367/2251799813685248), (68283603723515/2251799813685248)), (258007050634288699/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1036733968068099/1125899906842624), (65556679476195/1125899906842624)), (66985/140737488355328), by norm_num⟩
  | 2 => ⟨((1901624888351495/2251799813685248), (60364901030429/562949953421312)), (2098573/2251799813685248), by norm_num⟩
  | 3 => ⟨((1580013664603905/2251799813685248), (407820970531029/2251799813685248)), (249657/140737488355328), by norm_num⟩
  | 4 => ⟨((1034783475053565/2251799813685248), (286154525031469/1125899906842624)), (7052519/2251799813685248), by norm_num⟩
  | 5 => ⟨((165032252632533/1125899906842624), (525993424486099/2251799813685248)), (20133319/4503599627370496), by norm_num⟩
  | 6 => ⟨((-148971062123185/4503599627370496), (1233585745024485/18014398509481984)), (30616021/9007199254740992), by norm_num⟩
  | _ => zero

def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-345796421/134217728), (-4788662941/134217728)), (1/67108864), by norm_num⟩, -6, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-87955083/33554432), (-1218020837/33554432)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((55895550156577/4503599627370496), (161327208529419/2251799813685248)), (50227271/18014398509481984), by norm_num⟩
  | 1 => ⟨((-638763823/17179869184), (-1843616963/8589934592)), (145/17179869184), by norm_num⟩
  | 2 => ⟨((239195675/4294967296), (1380745709/4294967296)), (219/17179869184), by norm_num⟩
  | 3 => ⟨((-238855401/4294967296), (-689390747/2147483648)), (221/17179869184), by norm_num⟩
  | 4 => ⟨((715546833/17179869184), (1032615055/4294967296)), (21/2147483648), by norm_num⟩
  | 5 => ⟨((-107179337/4294967296), (-2474750597/17179869184)), (203/34359738368), by norm_num⟩
  | 6 => ⟨((428107465/34359738368), (4942460155/68719476736)), (205/68719476736), by norm_num⟩
  | 7 => ⟨((-732854485/137438953472), (-1057591957/34359738368)), (89/68719476736), by norm_num⟩
  | 8 => ⟨((274429479/137438953472), (6336524715/549755813888)), (269/549755813888), by norm_num⟩
  | 9 => ⟨((-365385443/549755813888), (-4218340353/1099511627776)), (181/1099511627776), by norm_num⟩
  | 10 => ⟨((875677571/4398046511104), (2527403667/2199023255552)), (219/4398046511104), by norm_num⟩
  | 11 => ⟨((-476962829/8796093022208), (-5506490715/17592186044416)), (241/17592186044416), by norm_num⟩
  | 12 => ⟨((952568627/70368744177664), (1374664329/17592186044416)), (243/70368744177664), by norm_num⟩
  | _ => zero

def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790280637907115/5070602400912917605986812821504), (1822695222929/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777924279449121/633825300114114700748351602688), (2155118998047/633825300114114700748351602688)), (361/9903520314283042199192993792), by norm_num⟩
  | 16 => ⟨((1888791905624859/39614081257132168796771975168), (2423958076591/39614081257132168796771975168)), (25995/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888507736009197/2475880078570760549798248448), (1287383422113/1237940039285380274899124224)), (3453/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1770174130227469/154742504910672534362390528), (2573992491049/154742504910672534362390528)), (6907/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((387150139201393/2417851639229258349412352), (1206147754379/4835703278458516698824704)), (25907/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257955077410637/604462909807314587353088), (2109936454583/604462909807314587353088)), (22673/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886437723269659/75557863725914323419136), (1713552992863/37778931862957161709568)), (9213/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1296523964039661/4722366482869645213696), (2568982043845/4722366482869645213696)), (27647/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810026112992735/295147905179352825856), (3530162048339/590295810358705651712)), (38027/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910865185294823/36893488147419103232), (1102355626411/18446744073709551616)), (743/1152921504606846976), by norm_num⟩
  | 7 => ⟨((1820695444170301/9223372036854775808), (4956094040303/9223372036854775808)), (26761/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1591944981837057/1152921504606846976), (4950466882557/1152921504606846976)), (53555/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596398077424771/72057594037927936), (4325335786443/144115188075855872)), (46897/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488962813394235/36028797018963968), (6475377726729/36028797018963968)), (70419/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485918516567993/9007199254740992), (8072170594501/9007199254740992)), (88153/9007199254740992), by norm_num⟩
  | 2 => ⟨((138830123911099/281474976710656), (2009795199541/562949953421312)), (88347/2251799813685248), by norm_num⟩
  | 1 => ⟨((551533804590455/562949953421312), (11976602420095/1125899906842624)), (133007/1125899906842624), by norm_num⟩
  | 0 => ⟨((540229705461721/562949953421312), (5906589586665/281474976710656)), (535945/2251799813685248), by norm_num⟩
  | _ => zero

def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((540229705461721/562949953421312), (5906589586665/281474976710656)), (2044467934615325217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2072714149371369/2251799813685248), (2834101977711/70368744177664)), (1051123/2251799813685248), by norm_num⟩
  | 2 => ⟨((1904218578271491/2251799813685248), (166957172210771/2251799813685248)), (2019723/2251799813685248), by norm_num⟩
  | 3 => ⟨((1597910113773829/2251799813685248), (282372302517529/2251799813685248)), (1857715/1125899906842624), by norm_num⟩
  | 4 => ⟨((1098491348759563/2251799813685248), (400751039501979/2251799813685248)), (3102433/1125899906842624), by norm_num⟩
  | 5 => ⟨((232276830577957/1125899906842624), (390995280507523/2251799813685248)), (16524735/4503599627370496), by norm_num⟩
  | 6 => ⟨((55895550156577/4503599627370496), (161327208529419/2251799813685248)), (50227271/18014398509481984), by norm_num⟩
  | _ => zero

def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-87955083/33554432), (-1218020837/33554432)), (1/67108864), by norm_num⟩, -6, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-178775137/67108864), (-4951432811/134217728)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((867148151287531/18014398509481984), (907373600577769/18014398509481984)), (36506729/18014398509481984), by norm_num⟩
  | 1 => ⟨((-1258874895/8589934592), (-658635923/4294967296)), (27/4294967296), by norm_num⟩
  | 2 => ⟨((119771027/536870912), (1002615923/4294967296)), (83/8589934592), by norm_num⟩
  | 3 => ⟨((-972388211/4294967296), (-508747779/2147483648)), (171/17179869184), by norm_num⟩
  | 4 => ⟨((2960457727/17179869184), (3097788057/17179869184)), (33/4294967296), by norm_num⟩
  | 5 => ⟨((-1802635995/17179869184), (-3772514099/34359738368)), (163/34359738368), by norm_num⟩
  | 6 => ⟨((914694289/17179869184), (1914250637/34359738368)), (167/68719476736), by norm_num⟩
  | 7 => ⟨((-3182636899/137438953472), (-3330273723/137438953472)), (147/137438953472), by norm_num⟩
  | 8 => ⟨((2422402363/274877906944), (633693317/68719476736)), (57/137438953472), by norm_num⟩
  | 9 => ⟨((-1638901855/549755813888), (-3429855151/1099511627776)), (39/274877906944), by norm_num⟩
  | 10 => ⟨((3991738777/4398046511104), (2088454193/2199023255552)), (3/68719476736), by norm_num⟩
  | 11 => ⟨((-552406285/2199023255552), (-2312125691/8796093022208)), (27/2199023255552), by norm_num⟩
  | 12 => ⟨((2242417773/35184372088832), (2346439515/35184372088832)), (111/35184372088832), by norm_num⟩
  | _ => zero

def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395126416376533/2535301200456458802993406410752), (1052591776005/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777860189260313/633825300114114700748351602688), (311119013887/158456325028528675187087900672)), (11541/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888719912097827/39614081257132168796771975168), (87482124135/2475880078570760549798248448)), (1623/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((944215692869479/1237940039285380274899124224), (185849020033/309485009821345068724781056)), (13797/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((442524485124601/38685626227668133590597632), (185792242703/19342813113834066795298816)), (27597/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387132324845911/2417851639229258349412352), (348239850855/2417851639229258349412352)), (25875/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((628946448736861/302231454903657293676544), (609178637745/302231454903657293676544)), (22643/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886336999897207/75557863725914323419136), (30920732785/1180591620717411303424)), (36799/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296448700356373/4722366482869645213696), (1483404913553/4722366482869645213696)), (6901/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((809974595491103/295147905179352825856), (1019199218001/295147905179352825856)), (37963/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910801127346119/36893488147419103232), (159129659731/4611686018427387904)), (47465/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820552244239633/9223372036854775808), (1430845748997/4611686018427387904)), (13353/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1591802942578701/1152921504606846976), (714598038465/288230376151711744)), (6679/144115188075855872), by norm_num⟩
  | 5 => ⟨((1192673172967161/144115188075855872), (156086647135/9007199254740992)), (23387/72057594037927936), by norm_num⟩
  | 4 => ⟨((744390468652757/18014398509481984), (3738678406877/36028797018963968)), (70203/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485695697333207/9007199254740992), (4660423974833/9007199254740992)), (87829/9007199254740992), by norm_num⟩
  | 2 => ⟨((2220849848325241/4503599627370496), (9282187342169/4503599627370496)), (43971/1125899906842624), by norm_num⟩
  | 1 => ⟨((2205520521612479/2251799813685248), (108023583105/17592186044416)), (264393/2251799813685248), by norm_num⟩
  | 0 => ⟨((2159821919555263/2251799813685248), (27271313969053/2251799813685248)), (531077/2251799813685248), by norm_num⟩
  | _ => zero

def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((2159821919555263/2251799813685248), (27271313969053/2251799813685248)), (2025897988326262717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2071270710335763/2251799813685248), (52314758467839/2251799813685248)), (1031633/2251799813685248), by norm_num⟩
  | 2 => ⟨((951999706076127/1125899906842624), (96241261122931/2251799813685248)), (1945787/2251799813685248), by norm_num⟩
  | 3 => ⟨((802902495851931/1125899906842624), (81376374351395/1125899906842624)), (3456829/2251799813685248), by norm_num⟩
  | 4 => ⟨((283342373360665/562949953421312), (29015587297339/281474976710656)), (2714985/1125899906842624), by norm_num⟩
  | 5 => ⟨((136628989574235/562949953421312), (233664689212719/2251799813685248)), (13170963/4503599627370496), by norm_num⟩
  | 6 => ⟨((867148151287531/18014398509481984), (907373600577769/18014398509481984)), (36506729/18014398509481984), by norm_num⟩
  | _ => zero

def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-178775137/67108864), (-4951432811/134217728)), (1/67108864), by norm_num⟩, -6, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨30,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 12 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨30,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 12 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨30,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 12 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨30,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 12 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨30,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 12 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨30,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiRectangle.Tile030Terms2
