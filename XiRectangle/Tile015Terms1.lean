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
namespace Reinmann.XiRectangle.Tile015Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨15,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (4371/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (4371/640))
  have he : value ((3/4), (4371/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_log9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((109861228866811/50000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log9 : Sound J_log9 F_log9 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log9_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-75496061613/34359738368), 0), (1/34359738368), by norm_num⟩
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
theorem S_negLog9 : Sound J_negLog9 F_negLog9 c := by
  apply sound_round (sound_scale (A_log9 hcre) S_log9)
  intro k
  fin_cases k <;> norm_num [J_negLog9, J_log9, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-55294967/33554432), (-64451813537/4294967296)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-75496061613/34359738368), 0), (1/34359738368), by norm_num⟩
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
theorem S_arg9 : Sound J_arg9 F_arg9 c := by
  apply sound_round (sound_mul (A_negLog9 hcre) (A_variable hcre) S_negLog9 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg9, J_negLog9, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-662005013611009/4503599627370496), (-139854772380489/1125899906842624)), (305867/1125899906842624), by norm_num⟩
  | 1 => ⟨((11097516527/34359738368), (37511272355/137438953472)), (21/34359738368), by norm_num⟩
  | 2 => ⟨((-48767472121/137438953472), (-41210344773/137438953472)), (47/68719476736), by norm_num⟩
  | 3 => ⟨((71435392213/274877906944), (30182794125/137438953472)), (141/274877906944), by norm_num⟩
  | 4 => ⟨((-19619949933/137438953472), (-8289797133/68719476736)), (79/274877906944), by norm_num⟩
  | 5 => ⟨((34487548959/549755813888), (29143273603/549755813888)), (71/549755813888), by norm_num⟩
  | 6 => ⟨((-25258963395/1099511627776), (-42689544683/2199023255552)), (53/1099511627776), by norm_num⟩
  | 7 => ⟨((31714065811/4398046511104), (26799576221/4398046511104)), (17/1099511627776), by norm_num⟩
  | 8 => ⟨((-69682924847/35184372088832), (-58884687535/35184372088832)), (19/4398046511104), by norm_num⟩
  | 9 => ⟨((34024230021/70368744177664), (28751751707/70368744177664)), (151/140737488355328), by norm_num⟩
  | 10 => ⟨((-29903549771/281474976710656), (-25269622197/281474976710656)), (135/562949953421312), by norm_num⟩
  | 11 => ⟨((47785319641/2251799813685248), (40380389055/2251799813685248)), (55/1125899906842624), by norm_num⟩
  | 12 => ⟨((-69996719167/18014398509481984), (-14787463879/4503599627370496)), (41/4503599627370496), by norm_num⟩
  | _ => zero

def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790914584677707/5070602400912917605986812821504), (-3178354993417/10141204801825835211973625643008)), (607/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((55606860446649/19807040628566084398385987584), (-3764066730893/633825300114114700748351602688)), (181/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((472618363382331/9903520314283042199192993792), (-4233942356629/39614081257132168796771975168)), (815/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890293615354715/2475880078570760549798248448), (-2248902701703/1237940039285380274899124224)), (433/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885979574451175/77371252455336267181195264), (-4496952251533/154742504910672534362390528)), (433/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387568274416999/2417851639229258349412352), (-2107493162659/4835703278458516698824704)), (203/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((78713602304789/37778931862957161709568), (-3687206695293/604462909807314587353088)), (711/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888812669805955/75557863725914323419136), (-5990011644931/75557863725914323419136)), (1155/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649151838089041/2361183241434822606848), (-2245511027383/2361183241434822606848)), (867/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622496897729941/590295810358705651712), (-6172739756849/590295810358705651712)), (149/73786976294838206464), by norm_num⟩
  | 8 => ⟨((456195641021623/18446744073709551616), (-7712301842831/73786976294838206464)), (373/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1824124152388845/9223372036854775808), (-2167839740885/2305843009213693952)), (1679/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595367434278011/1152921504606846976), (-8665134425185/1152921504606846976)), (1681/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597891885653663/72057594037927936), (-7574991704469/144115188075855872)), (1473/144115188075855872), by norm_num⟩
  | 4 => ⟨((93339387501305/2251799813685248), (-5674244979109/18014398509481984)), (2213/36028797018963968), by norm_num⟩
  | 3 => ⟨((745739115007287/4503599627370496), (-7080563114007/4503599627370496)), (1387/4503599627370496), by norm_num⟩
  | 2 => ⟨((558082009229805/1125899906842624), (-14124416166121/2251799813685248)), (87/70368744177664), by norm_num⟩
  | 1 => ⟨((1111260761165889/1125899906842624), (-21094917036571/1125899906842624)), (2101/562949953421312), by norm_num⟩
  | 0 => ⟨((548241059613673/562949953421312), (-10455854225147/281474976710656)), (2127/281474976710656), by norm_num⟩
  | _ => zero

def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((548241059613673/562949953421312), (-10455854225147/281474976710656)), (8113862157726199/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1066279366654089/1125899906842624), (-40730644454077/562949953421312)), (17205/1125899906842624), by norm_num⟩
  | 2 => ⟨((501961026594019/562949953421312), (-77147614113759/562949953421312)), (35079/1125899906842624), by norm_num⟩
  | 3 => ⟨((437007084485465/562949953421312), (-275158353558579/1125899906842624)), (72173/1125899906842624), by norm_num⟩
  | 4 => ⟨((305617152930927/562949953421312), (-427200141432335/1125899906842624)), (73665/562949953421312), by norm_num⟩
  | 5 => ⟨((339474965156611/2251799813685248), (-927682399920397/2251799813685248)), (135885/562949953421312), by norm_num⟩
  | 6 => ⟨((-662005013611009/4503599627370496), (-139854772380489/1125899906842624)), (305867/1125899906842624), by norm_num⟩
  | _ => zero

def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-55294967/33554432), (-64451813537/4294967296)), (1/2147483648), by norm_num⟩, -2, term9ValuePoly, term9ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term9Value_checks : CertifiedScalarExp.Checks term9Value := by
  constructor
  · norm_num [term9Value, CertifiedScalarExp.reduced, term9ValuePoly, term9ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term9Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term9ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term9Value, term9ValueSquares, term9ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term9Value, CertifiedScalarExp.roundingCheck, term9ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term9 : Sound J_term9 F_term9 c := by
  apply exp_sound (A_arg9 hcre) S_arg9 term9Value term9Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term9Value,J_arg9]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term9,J_arg9,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1151292546497023/500000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log10 : Sound J_log10 F_log10 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log10_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-79116221365/34359738368), 0), (1/34359738368), by norm_num⟩
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
theorem S_negLog10 : Sound J_negLog10 F_negLog10 c := by
  apply sound_round (sound_scale (A_log10 hcre) S_log10)
  intro k
  fin_cases k <;> norm_num [J_negLog10, J_log10, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-7417145753/4294967296), (-67542383513/4294967296)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-79116221365/34359738368), 0), (1/34359738368), by norm_num⟩
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
theorem S_arg10 : Sound J_arg10 F_arg10 c := by
  apply sound_round (sound_mul (A_negLog10 hcre) (A_variable hcre) S_negLog10 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg10, J_negLog10, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1601472991626069/9007199254740992), (28786949347893/9007199254740992)), (503671/2251799813685248), by norm_num⟩
  | 1 => ⟨((7033401179/17179869184), (-2022839369/274877906944)), (9/17179869184), by norm_num⟩
  | 2 => ⟨((-64780018831/137438953472), (145554993/17179869184)), (21/34359738368), by norm_num⟩
  | 3 => ⟨((99441003789/274877906944), (-1787481371/274877906944)), (131/274877906944), by norm_num⟩
  | 4 => ⟨((-57242843239/274877906944), (2057913979/549755813888)), (153/549755813888), by norm_num⟩
  | 5 => ⟨((52722607009/549755813888), (-473852205/274877906944)), (143/1099511627776), by norm_num⟩
  | 6 => ⟨((-80932192641/2199023255552), (1454780031/2199023255552)), (7/137438953472), by norm_num⟩
  | 7 => ⟨((26621894331/2199023255552), (-1914145607/8796093022208)), (75/4398046511104), by norm_num⟩
  | 8 => ⟨((-122598354067/35184372088832), (1101870785/17592186044416)), (175/35184372088832), by norm_num⟩
  | 9 => ⟨((15682952361/17592186044416), (-1127622775/70368744177664)), (91/70368744177664), by norm_num⟩
  | 10 => ⟨((-115556263425/562949953421312), (1038578957/281474976710656)), (85/281474976710656), by norm_num⟩
  | 11 => ⟨((48377841739/1125899906842624), (-1739211945/2251799813685248)), (145/2251799813685248), by norm_num⟩
  | 12 => ⟨((-74262731479/9007199254740992), (1334894499/9007199254740992)), (113/9007199254740992), by norm_num⟩
  | _ => zero

def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790863118239471/5070602400912917605986812821504), (4068862884719/10141204801825835211973625643008)), (19/316912650057057350374175801344), by norm_num⟩
  | 17 => ⟨((1779292802428517/633825300114114700748351602688), (2409025348283/316912650057057350374175801344)), (725/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472582656095865/9903520314283042199192993792), (2709723070837/19807040628566084398385987584)), (51/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((1890141528626029/2475880078570760549798248448), (5757142733387/2475880078570760549798248448)), (867/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771806690283893/154742504910672534362390528), (2877998200429/77371252455336267181195264)), (867/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550129772815719/9671406556917033397649408), (2697514311471/4835703278458516698824704)), (407/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259291832997871/604462909807314587353088), (4719432014315/604462909807314587353088)), (89/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1888607499128005/75557863725914323419136), (3833396578459/37778931862957161709568)), (579/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298149151778347/4722366482869645213696), (5748096426653/4722366482869645213696)), (869/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622283377347751/590295810358705651712), (7900385012701/590295810358705651712)), (1195/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912257045726389/36893488147419103232), (4935304860079/36893488147419103232)), (1495/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455954990488857/2305843009213693952), (11097737264973/9223372036854775808)), (421/2305843009213693952), by norm_num⟩
  | 6 => ⟨((199382568741723/144115188075855872), (346542609203/36028797018963968)), (843/576460752303423488), by norm_num⟩
  | 5 => ⟨((597756111514017/72057594037927936), (4846885993193/72057594037927936)), (739/72057594037927936), by norm_num⟩
  | 4 => ⟨((1493016844068921/36028797018963968), (14521814434599/36028797018963968)), (2221/36028797018963968), by norm_num⟩
  | 3 => ⟨((1490951011078007/9007199254740992), (18119288811539/9007199254740992)), (1393/4503599627370496), by norm_num⟩
  | 2 => ⟨((557810541430101/1125899906842624), (18069814225821/2251799813685248)), (2799/2251799813685248), by norm_num⟩
  | 1 => ⟨((1110407308588891/1125899906842624), (26981016217869/1125899906842624)), (529/140737488355328), by norm_num⟩
  | 0 => ⟨((1094620470752483/1125899906842624), (3341694462233/70368744177664)), (8597/1125899906842624), by norm_num⟩
  | _ => zero

def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((1094620470752483/1125899906842624), (3341694462233/70368744177664)), (32794956687545421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1061670967130177/1125899906842624), (103963406143079/1125899906842624)), (8767/562949953421312), by norm_num⟩
  | 2 => ⟨((991506301622151/1125899906842624), (196065261708025/1125899906842624)), (18153/562949953421312), by norm_num⟩
  | 3 => ⟨((839011668414535/1125899906842624), (21582729216341/70368744177664)), (38295/562949953421312), by norm_num⟩
  | 4 => ⟨((259655472423997/562949953421312), (1029329817398627/2251799813685248)), (322261/2251799813685248), by norm_num⟩
  | 5 => ⟨((4266710711359/1125899906842624), (1899075528063655/4503599627370496)), (1183801/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1601472991626069/9007199254740992), (28786949347893/9007199254740992)), (503671/2251799813685248), by norm_num⟩
  | _ => zero

def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-7417145753/4294967296), (-67542383513/4294967296)), (1/2147483648), by norm_num⟩, -3, term10ValuePoly, term10ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term10Value_checks : CertifiedScalarExp.Checks term10Value := by
  constructor
  · norm_num [term10Value, CertifiedScalarExp.reduced, term10ValuePoly, term10ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term10Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term10ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term10Value, term10ValueSquares, term10ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term10Value, CertifiedScalarExp.roundingCheck, term10ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term10 : Sound J_term10 F_term10 c := by
  apply exp_sound (A_arg10 hcre) S_arg10 term10Value term10Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term10Value,J_arg10]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term10,J_arg10,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((239789527279837/100000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log11 : Sound J_log11 F_log11 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log11_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-82391054207/34359738368), 0), (1/34359738368), by norm_num⟩
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
theorem S_negLog11 : Sound J_negLog11 F_negLog11 c := by
  apply sound_round (sound_scale (A_log11 hcre) S_log11)
  intro k
  fin_cases k <;> norm_num [J_negLog11, J_log11, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1931040333/1073741824), (-70338144129/4294967296)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-82391054207/34359738368), 0), (1/34359738368), by norm_num⟩
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
theorem S_arg11 : Sound J_arg11 F_arg11 c := by
  apply sound_round (sound_mul (A_negLog11 hcre) (A_variable hcre) S_negLog11 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg11, J_negLog11, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-146233350112021/1125899906842624), (924762117442819/9007199254740992)), (32941/140737488355328), by norm_num⟩
  | 1 => ⟨((21402115415/68719476736), (-4229512615/17179869184)), (79/137438953472), by norm_num⟩
  | 2 => ⟨((-51320031381/137438953472), (40567713223/137438953472)), (97/137438953472), by norm_num⟩
  | 3 => ⟨((5127502527/17179869184), (-32425709255/137438953472)), (79/137438953472), by norm_num⟩
  | 4 => ⟨((-49180856283/274877906944), (19438363735/137438953472)), (97/274877906944), by norm_num⟩
  | 5 => ⟨((47172217117/549755813888), (-37288928409/549755813888)), (95/549755813888), by norm_num⟩
  | 6 => ⟨((-75409357621/2199023255552), (3725622715/137438953472)), (155/2199023255552), by norm_num⟩
  | 7 => ⟨((12915981583/1099511627776), (-40839557013/4398046511104)), (109/4398046511104), by norm_num⟩
  | 8 => ⟨((-61942342363/17592186044416), (3060280647/1099511627776)), (133/17592186044416), by norm_num⟩
  | 9 => ⟨((66013888861/70368744177664), (-13045746661/17592186044416)), (9/4398046511104), by norm_num⟩
  | 10 => ⟨((-63317756815/281474976710656), (25025867399/140737488355328)), (141/281474976710656), by norm_num⟩
  | 11 => ⟨((55210672637/1125899906842624), (-43643206643/1125899906842624)), (125/1125899906842624), by norm_num⟩
  | 12 => ⟨((-44129803641/4503599627370496), (8720986575/1125899906842624)), (51/2251799813685248), by norm_num⟩
  | _ => zero

def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790816561182973/5070602400912917605986812821504), (3220942493329/10141204801825835211973625643008)), (607/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889593591993627/316912650057057350374175801344), (3813555515351/633825300114114700748351602688)), (181/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1890212090653297/39614081257132168796771975168), (4289553872659/39614081257132168796771975168)), (815/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890015951428663/2475880078570760549798248448), (2278406370745/1237940039285380274899124224)), (433/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((442920380853167/38685626227668133590597632), (4555869739801/154742504910672534362390528)), (433/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((775006432317529/4835703278458516698824704), (4270126045755/9671406556917033397649408)), (203/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1259189973864577/604462909807314587353088), (1867679285749/302231454903657293676544)), (711/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888442794143173/75557863725914323419136), (6068079704777/75557863725914323419136)), (1155/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298026336630955/4722366482869645213696), (4549416800003/4722366482869645213696)), (867/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202764458145529/73786976294838206464), (6252778726425/590295810358705651712)), (1193/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912153093770905/36893488147419103232), (3905985082623/36893488147419103232)), (373/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1823588454815815/9223372036854775808), (8782963307543/9223372036854775808)), (1679/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398708004932027/288230376151711744), (8776086396115/1152921504606846976)), (841/576460752303423488), by norm_num⟩
  | 5 => ⟨((1195315602626411/144115188075855872), (7671341825269/144115188075855872)), (1473/144115188075855872), by norm_num⟩
  | 4 => ⟨((373182146679447/9007199254740992), (11491552096395/36028797018963968)), (1107/18014398509481984), by norm_num⟩
  | 3 => ⟨((1490602336518149/9007199254740992), (3584349892395/2251799813685248)), (1387/4503599627370496), by norm_num⟩
  | 2 => ⟨((1115289816876389/2251799813685248), (1787108749583/281474976710656)), (2785/2251799813685248), by norm_num⟩
  | 1 => ⟨((138744214207711/140737488355328), (10672045471475/562949953421312)), (4203/1125899906842624), by norm_num⟩
  | 0 => ⟨((1093885192923501/1125899906842624), (42283988886213/1125899906842624)), (8513/1125899906842624), by norm_num⟩
  | _ => zero

def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((1093885192923501/1125899906842624), (42283988886213/1125899906842624)), (32474522117232921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((132649100546129/140737488355328), (82163306097219/1125899906842624)), (8591/562949953421312), by norm_num⟩
  | 2 => ⟨((124276073784711/140737488355328), (38720630796591/281474976710656)), (17449/562949953421312), by norm_num⟩
  | 3 => ⟨((856614446037239/1125899906842624), (136766629164745/562949953421312)), (71235/1125899906842624), by norm_num⟩
  | 4 => ⟨((585281037632635/1125899906842624), (208111341987551/562949953421312)), (4469/35184372088832), by norm_num⟩
  | 5 => ⟨((300759542349909/2251799813685248), (432733394651997/1125899906842624)), (508831/2251799813685248), by norm_num⟩
  | 6 => ⟨((-146233350112021/1125899906842624), (924762117442819/9007199254740992)), (32941/140737488355328), by norm_num⟩
  | _ => zero

def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1931040333/1073741824), (-70338144129/4294967296)), (1/2147483648), by norm_num⟩, -3, term11ValuePoly, term11ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term11Value_checks : CertifiedScalarExp.Checks term11Value := by
  constructor
  · norm_num [term11Value, CertifiedScalarExp.reduced, term11ValuePoly, term11ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term11Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term11ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term11Value, term11ValueSquares, term11ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term11Value, CertifiedScalarExp.roundingCheck, term11ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term11 : Sound J_term11 F_term11 c := by
  apply exp_sound (A_arg11 hcre) S_arg11 term11Value term11Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term11Value,J_arg11]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term11,J_arg11,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log12 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((621226662447/250000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log12 : Sound J_log12 F_log12 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log12_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog12 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-21345185589/8589934592), 0), (1/34359738368), by norm_num⟩
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
theorem S_negLog12 : Sound J_negLog12 F_negLog12 c := by
  apply sound_round (sound_scale (A_log12 hcre) S_log12)
  intro k
  fin_cases k <;> norm_num [J_negLog12, J_log12, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg12 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-2001111149/1073741824), (-72890473601/4294967296)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-21345185589/8589934592), 0), (1/34359738368), by norm_num⟩
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
theorem S_arg12 : Sound J_arg12 F_arg12 c := by
  apply sound_round (sound_mul (A_negLog12 hcre) (A_variable hcre) S_negLog12 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg12, J_negLog12, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term12 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-211505755656429/4503599627370496), (1331441713043125/9007199254740992)), (942783/4503599627370496), by norm_num⟩
  | 1 => ⟨((32078372723/274877906944), (-50483831277/137438953472)), (73/137438953472), by norm_num⟩
  | 2 => ⟨((-2490992553/17179869184), (7840475503/17179869184)), (93/137438953472), by norm_num⟩
  | 3 => ⟨((33012714451/274877906944), (-103908531813/274877906944)), (157/274877906944), by norm_num⟩
  | 4 => ⟨((-20508378417/274877906944), (32275375209/137438953472)), (99/274877906944), by norm_num⟩
  | 5 => ⟨((10192281181/274877906944), (-64161035585/549755813888)), (25/137438953472), by norm_num⟩
  | 6 => ⟨((-16884578189/1099511627776), (26572363997/549755813888)), (85/1099511627776), by norm_num⟩
  | 7 => ⟨((23975200355/4398046511104), (-37731339427/2199023255552)), (123/4398046511104), by norm_num⟩
  | 8 => ⟨((-7447016849/4398046511104), (11719857031/2199023255552)), (155/17592186044416), by norm_num⟩
  | 9 => ⟨((16449014835/35184372088832), (-103547557941/70368744177664)), (87/35184372088832), by norm_num⟩
  | 10 => ⟨((-32699413077/281474976710656), (102922406119/281474976710656)), (175/281474976710656), by norm_num⟩
  | 11 => ⟨((29547268727/1125899906842624), (-93000935047/1125899906842624)), (5/35184372088832), by norm_num⟩
  | 12 => ⟨((-24474068181/4503599627370496), (77032880645/4503599627370496)), (135/4503599627370496), by norm_num⟩
  | _ => zero

def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790774057920435/5070602400912917605986812821504), (611712956149/2535301200456458802993406410752)), (607/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444772457987631/158456325028528675187087900672), (2896730001127/633825300114114700748351602688)), (181/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((945051388450077/19807040628566084398385987584), (407285084209/4951760157141521099596496896)), (407/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((472475017528781/618970019642690137449562112), (3461264194553/2475880078570760549798248448)), (865/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885782969778609/77371252455336267181195264), (3460522920323/154742504910672534362390528)), (865/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193738102582493/1208925819614629174706176), (810863195809/2417851639229258349412352)), (203/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((39346742221751/18889465931478580854784), (22165889833/4722366482869645213696)), (355/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1888290273718191/75557863725914323419136), (4609029279395/75557863725914323419136)), (577/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297912463557741/4722366482869645213696), (1727740493059/2361183241434822606848)), (433/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810979964748589/295147905179352825856), (2374594596461/295147905179352825856)), (1191/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824112776419489/73786976294838206464), (2966670958565/36893488147419103232)), (1489/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823372595655027/9223372036854775808), (1667671942377/2305843009213693952)), (419/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1594618317959467/1152921504606846976), (3332644131739/576460752303423488)), (839/576460752303423488), by norm_num⟩
  | 5 => ⟨((1195131036456911/144115188075855872), (1456514177309/36028797018963968)), (735/72057594037927936), by norm_num⟩
  | 4 => ⟨((1492456572756581/36028797018963968), (8726953828777/36028797018963968)), (2207/36028797018963968), by norm_num⟩
  | 3 => ⟨((745135378653657/4503599627370496), (10887484691767/9007199254740992)), (691/2251799813685248), by norm_num⟩
  | 2 => ⟨((2229941696063653/4503599627370496), (10855717435251/2251799813685248)), (5543/4503599627370496), by norm_num⟩
  | 1 => ⟨((138688327756567/140737488355328), (16204312484677/1125899906842624)), (8355/2251799813685248), by norm_num⟩
  | 0 => ⟨((2186230945165353/2251799813685248), (32092497139367/1125899906842624)), (16871/2251799813685248), by norm_num⟩
  | _ => zero

def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((2186230945165353/2251799813685248), (32092497139367/1125899906842624)), (64357766158293967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2120741818648867/2251799813685248), (124632056415157/2251799813685248)), (33723/2251799813685248), by norm_num⟩
  | 2 => ⟨((1990413483756651/2251799813685248), (117378291079641/1125899906842624)), (67255/2251799813685248), by norm_num⟩
  | 3 => ⟨((1734894531792177/2251799813685248), (415012616743891/2251799813685248)), (16615/281474976710656), by norm_num⟩
  | 4 => ⟨((630079003280001/1125899906842624), (639491232780055/2251799813685248)), (63453/562949953421312), by norm_num⟩
  | 5 => ⟨((65450376490457/281474976710656), (178936864683779/562949953421312)), (26765/140737488355328), by norm_num⟩
  | 6 => ⟨((-211505755656429/4503599627370496), (1331441713043125/9007199254740992)), (942783/4503599627370496), by norm_num⟩
  | _ => zero

def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2001111149/1073741824), (-72890473601/4294967296)), (1/2147483648), by norm_num⟩, -3, term12ValuePoly, term12ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term12Value_checks : CertifiedScalarExp.Checks term12Value := by
  constructor
  · norm_num [term12Value, CertifiedScalarExp.reduced, term12ValuePoly, term12ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term12Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term12ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term12Value, term12ValueSquares, term12ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term12Value, CertifiedScalarExp.roundingCheck, term12ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term12 : Sound J_term12 F_term12 c := by
  apply exp_sound (A_arg12 hcre) S_arg12 term12Value term12Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term12Value,J_arg12]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term12,J_arg12,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log13 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((80154667420673/31250000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log13 : Sound J_log13 F_log13 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log13_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog13 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-44065494425/17179869184), 0), (1/34359738368), by norm_num⟩
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
theorem S_negLog13 : Sound J_negLog13 F_negLog13 c := by
  apply sound_round (sound_scale (A_log13 hcre) S_log13)
  intro k
  fin_cases k <;> norm_num [J_negLog13, J_log13, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg13 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-8262280205/4294967296), (-37619194557/2147483648)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-44065494425/17179869184), 0), (1/34359738368), by norm_num⟩
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
theorem S_arg13 : Sound J_arg13 F_arg13 c := by
  apply sound_round (sound_mul (A_negLog13 hcre) (A_variable hcre) S_negLog13 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg13, J_negLog13, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term13 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((311504469881829/9007199254740992), (1278215634829103/9007199254740992)), (1520959/9007199254740992), by norm_num⟩
  | 1 => ⟨((-24383337093/274877906944), (-100053661233/274877906944)), (61/137438953472), by norm_num⟩
  | 2 => ⟨((7817753101/68719476736), (64158143523/137438953472)), (5/8589934592), by norm_num⟩
  | 3 => ⟨((-6684046931/68719476736), (-109708259337/274877906944)), (35/68719476736), by norm_num⟩
  | 4 => ⟨((17144241881/274877906944), (17587258081/68719476736)), (91/274877906944), by norm_num⟩
  | 5 => ⟨((-17589644879/549755813888), (-72176682103/549755813888)), (95/549755813888), by norm_num⟩
  | 6 => ⟨((3759712361/274877906944), (61709844795/1099511627776)), (83/1099511627776), by norm_num⟩
  | 7 => ⟨((-5510555317/1099511627776), (-45223607645/2199023255552)), (31/1099511627776), by norm_num⟩
  | 8 => ⟨((1766786915/1099511627776), (28999065843/4398046511104)), (81/8796093022208), by norm_num⟩
  | 9 => ⟨((-16112778533/35184372088832), (-8264570589/4398046511104)), (47/17592186044416), by norm_num⟩
  | 10 => ⟨((8265692189/70368744177664), (67834256071/140737488355328)), (49/70368744177664), by norm_num⟩
  | 11 => ⟨((-1927371079/70368744177664), (-63269611463/562949953421312)), (93/562949953421312), by norm_num⟩
  | 12 => ⟨((13182957895/2251799813685248), (108188899513/4503599627370496)), (81/2251799813685248), by norm_num⟩
  | _ => zero

def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581469917418141/10141204801825835211973625643008), (867378719033/5070602400912917605986812821504)), (607/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778999492919759/633825300114114700748351602688), (1026753270129/316912650057057350374175801344)), (723/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236250161311999/4951760157141521099596496896), (288725365107/4951760157141521099596496896)), (813/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((118112026651141/154742504910672534362390528), (2453683756879/2475880078570760549798248448)), (27/77371252455336267181195264), by norm_num⟩
  | 14 => ⟨((1771458504540315/154742504910672534362390528), (2453141822573/154742504910672534362390528)), (27/4835703278458516698824704), by norm_num⟩
  | 13 => ⟨((774902160968995/4835703278458516698824704), (574811199017/2417851639229258349412352)), (405/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629504018095081/302231454903657293676544), (2011263694373/604462909807314587353088)), (709/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472037037996509/18889465931478580854784), (3267224777539/75557863725914323419136)), (1153/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297806235097581/4722366482869645213696), (2449475038751/4722366482869645213696)), (865/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810907227229149/295147905179352825856), (841623889305/147573952589676412928)), (1189/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911965907676557/36893488147419103232), (1051455408017/18446744073709551616)), (1487/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823170226736799/9223372036854775808), (591048956975/1152921504606846976)), (1673/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594417462181739/1152921504606846976), (1181111819013/288230376151711744)), (837/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194956986896759/144115188075855872), (4129457678029/144115188075855872)), (733/72057594037927936), by norm_num⟩
  | 4 => ⟨((746099444660661/18014398509481984), (1546332120101/9007199254740992)), (2201/36028797018963968), by norm_num⟩
  | 3 => ⟨((1489954570052407/9007199254740992), (964522504347/1125899906842624)), (2755/9007199254740992), by norm_num⟩
  | 2 => ⟨((1114663502305077/2251799813685248), (7693001139257/2251799813685248)), (5519/4503599627370496), by norm_num⟩
  | 1 => ⟨((2218135176877445/2251799813685248), (22963402218405/2251799813685248)), (2077/562949953421312), by norm_num⟩
  | 0 => ⟨((2184649268596363/2251799813685248), (45466156163671/2251799813685248)), (8365/1125899906842624), by norm_num⟩
  | _ => zero

def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((2184649268596363/2251799813685248), (45466156163671/2251799813685248)), (31909946921920421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2118583200171253/2251799813685248), (88220635071725/2251799813685248)), (33139/2251799813685248), by norm_num⟩
  | 2 => ⟨((497447849089939/562949953421312), (166002993903365/2251799813685248)), (64955/2251799813685248), by norm_num⟩
  | 3 => ⟨((1746031233836843/2251799813685248), (146687697117399/1125899906842624)), (31093/562949953421312), by norm_num⟩
  | 4 => ⟨((657819564951231/1125899906842624), (454962824368325/2251799813685248)), (225283/2251799813685248), by norm_num⟩
  | 5 => ⟨((676754274208459/2251799813685248), (265817099172021/1125899906842624)), (354283/2251799813685248), by norm_num⟩
  | 6 => ⟨((311504469881829/9007199254740992), (1278215634829103/9007199254740992)), (1520959/9007199254740992), by norm_num⟩
  | _ => zero

def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-8262280205/4294967296), (-37619194557/2147483648)), (1/2147483648), by norm_num⟩, -3, term13ValuePoly, term13ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term13Value_checks : CertifiedScalarExp.Checks term13Value := by
  constructor
  · norm_num [term13Value, CertifiedScalarExp.reduced, term13ValuePoly, term13ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term13Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term13ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term13Value, term13ValueSquares, term13ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term13Value, CertifiedScalarExp.roundingCheck, term13ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term13 : Sound J_term13 F_term13 c := by
  apply exp_sound (A_arg13 hcre) S_arg13 term13Value term13Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term13Value,J_arg13]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term13,J_arg13,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log14 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1319528664807629/500000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log14 : Sound J_log14 F_log14 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log14_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog14 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-11334664923/4294967296), 0), (1/34359738368), by norm_num⟩
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
theorem S_negLog14 : Sound J_negLog14 F_negLog14 c := by
  apply sound_round (sound_scale (A_log14 hcre) S_log14)
  intro k
  fin_cases k <;> norm_num [J_negLog14, J_log14, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg14 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-2125249673/1073741824), (-77412219341/4294967296)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-11334664923/4294967296), 0), (1/34359738368), by norm_num⟩
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
theorem S_arg14 : Sound J_arg14 F_arg14 c := by
  apply sound_round (sound_mul (A_negLog14 hcre) (A_variable hcre) S_negLog14 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg14, J_negLog14, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term14 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((843895817131205/9007199254740992), (914664880803871/9007199254740992)), (565285/4503599627370496), by norm_num⟩
  | 1 => ⟨((-33982688013/137438953472), (-36832474637/137438953472)), (47/137438953472), by norm_num⟩
  | 2 => ⟨((44841130941/137438953472), (48601506079/137438953472)), (65/137438953472), by norm_num⟩
  | 3 => ⟨((-39446105093/137438953472), (-2672128351/8589934592)), (59/137438953472), by norm_num⟩
  | 4 => ⟨((52050266385/274877906944), (56415199283/274877906944)), (5/17179869184), by norm_num⟩
  | 5 => ⟨((-54945454805/549755813888), (-14888294517/137438953472)), (43/274877906944), by norm_num⟩
  | 6 => ⟨((24167367539/549755813888), (26194041847/549755813888)), (39/549755813888), by norm_num⟩
  | 7 => ⟨((-36445181967/2199023255552), (-617210519/34359738368)), (61/2199023255552), by norm_num⟩
  | 8 => ⟨((12022615575/2199023255552), (52123326211/8796093022208)), (83/8796093022208), by norm_num⟩
  | 9 => ⟨((-28202997115/17592186044416), (-30568099129/17592186044416)), (25/8796093022208), by norm_num⟩
  | 10 => ⟨((59543461003/140737488355328), (64536772847/140737488355328)), (27/35184372088832), by norm_num⟩
  | 11 => ⟨((-28570655853/281474976710656), (-61933179423/562949953421312)), (53/281474976710656), by norm_num⟩
  | 12 => ⟨((50266399161/2251799813685248), (27240868517/1125899906842624)), (3/70368744177664), by norm_num⟩
  | _ => zero

def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581397516987371/10141204801825835211973625643008), (1075461013921/10141204801825835211973625643008)), (607/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778915182376157/633825300114114700748351602688), (318238107427/158456325028528675187087900672)), (361/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889906536718921/39614081257132168796771975168), (715911496583/19807040628566084398385987584)), (813/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236211484133693/309485009821345068724781056), (23765699339/38685626227668133590597632)), (27/77371252455336267181195264), by norm_num⟩
  | 14 => ⟨((1771358088956781/154742504910672534362390528), (380164825351/38685626227668133590597632)), (863/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549710328625979/9671406556917033397649408), (712625576229/4835703278458516698824704)), (809/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258925938251991/604462909807314587353088), (1246727933593/604462909807314587353088)), (709/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888015016793659/75557863725914323419136), (506311336453/18889465931478580854784)), (1151/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297706623229613/4722366482869645213696), (1518332656505/4722366482869645213696)), (27/147573952589676412928), by norm_num⟩
  | 9 => ⟨((810838938510609/295147905179352825856), (1043365336551/295147905179352825856)), (297/147573952589676412928), by norm_num⟩
  | 8 => ⟨((911880838134361/36893488147419103232), (2606949066959/73786976294838206464)), (371/18446744073709551616), by norm_num⟩
  | 7 => ⟨((911489810252609/4611686018427387904), (1465402827331/4611686018427387904)), (835/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1594227854763697/1152921504606846976), (732073148419/288230376151711744)), (1671/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194792202032513/144115188075855872), (2559431568237/144115188075855872)), (731/72057594037927936), by norm_num⟩
  | 4 => ⟨((745976975094217/18014398509481984), (1916752649545/18014398509481984)), (2195/36028797018963968), by norm_num⟩
  | 3 => ⟨((372413075372585/2251799813685248), (4782023422765/9007199254740992)), (1373/4503599627370496), by norm_num⟩
  | 2 => ⟨((2228734137917653/4503599627370496), (4767266858985/2251799813685248)), (2749/2251799813685248), by norm_num⟩
  | 1 => ⟨((1108637446824929/1125899906842624), (14228232506409/2251799813685248)), (1033/281474976710656), by norm_num⟩
  | 0 => ⟨((2183043817282025/2251799813685248), (28163477892681/2251799813685248)), (16599/2251799813685248), by norm_num⟩
  | _ => zero

def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((2183043817282025/2251799813685248), (28163477892681/2251799813685248)), (63320168502043967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1058017479557419/1125899906842624), (6825885000203/281474976710656)), (4075/281474976710656), by norm_num⟩
  | 2 => ⟨((1987131355023411/2251799813685248), (12828681483625/281474976710656)), (62851/2251799813685248), by norm_num⟩
  | 3 => ⟨((1748893571174579/2251799813685248), (181133509753689/2251799813685248)), (58329/1125899906842624), by norm_num⟩
  | 4 => ⟨((167966716920769/281474976710656), (281360029259505/2251799813685248)), (199977/2251799813685248), by norm_num⟩
  | 5 => ⟨((1533401748240381/4503599627370496), (671592493794301/4503599627370496)), (144321/1125899906842624), by norm_num⟩
  | 6 => ⟨((843895817131205/9007199254740992), (914664880803871/9007199254740992)), (565285/4503599627370496), by norm_num⟩
  | _ => zero

def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2125249673/1073741824), (-77412219341/4294967296)), (1/2147483648), by norm_num⟩, -3, term14ValuePoly, term14ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term14Value_checks : CertifiedScalarExp.Checks term14Value := by
  constructor
  · norm_num [term14Value, CertifiedScalarExp.reduced, term14ValuePoly, term14ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term14Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term14ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term14Value, term14ValueSquares, term14ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term14Value, CertifiedScalarExp.roundingCheck, term14ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term14 : Sound J_term14 F_term14 c := by
  apply exp_sound (A_arg14 hcre) S_arg14 term14Value term14Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term14Value,J_arg14]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term14,J_arg14,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log15 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((270805020110221/100000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log15 : Sound J_log15 F_log15 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log15_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog15 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-93047896397/34359738368), 0), (1/34359738368), by norm_num⟩
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
theorem S_negLog15 : Sound J_negLog15 F_negLog15 c := by
  apply sound_round (sound_scale (A_log15 hcre) S_log15)
  intro k
  fin_cases k <;> norm_num [J_negLog15, J_log15, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg15 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-8723240287/4294967296), (-79436006865/4294967296)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-93047896397/34359738368), 0), (1/34359738368), by norm_num⟩
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
theorem S_arg15 : Sound J_arg15 F_arg15 c := by
  apply sound_round (sound_mul (A_negLog15 hcre) (A_variable hcre) S_negLog15 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg15, J_negLog15, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term15 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((34634098174897/281474976710656), (410117361130145/9007199254740992)), (779483/9007199254740992), by norm_num⟩
  | 1 => ⟨((-91592652859/274877906944), (-33893383859/274877906944)), (67/274877906944), by norm_num⟩
  | 2 => ⟨((31004687749/68719476736), (5736561561/34359738368)), (47/137438953472), by norm_num⟩
  | 3 => ⟨((-55974833929/137438953472), (-20713195585/137438953472)), (11/34359738368), by norm_num⟩
  | 4 => ⟨((75791330139/274877906944), (28046186735/274877906944)), (31/137438953472), by norm_num⟩
  | 5 => ⟨((-41049345365/274877906944), (-30380192651/549755813888)), (69/549755813888), by norm_num⟩
  | 6 => ⟨((37054562657/549755813888), (13711847803/549755813888)), (1/17179869184), by norm_num⟩
  | 7 => ⟨((-57340351917/2199023255552), (-663078075/68719476736)), (51/2199023255552), by norm_num⟩
  | 8 => ⟨((38820137885/4398046511104), (14365189715/4398046511104)), (71/8796093022208), by norm_num⟩
  | 9 => ⟨((-23361529379/8796093022208), (-34579248797/35184372088832)), (11/4398046511104), by norm_num⟩
  | 10 => ⟨((25305677733/35184372088832), (4682117083/17592186044416)), (49/70368744177664), by norm_num⟩
  | 11 => ⟨((-99678611889/562949953421312), (-9221387715/140737488355328)), (99/562949953421312), by norm_num⟩
  | 12 => ⟨((22494557081/562949953421312), (33295974475/2251799813685248)), (23/562949953421312), by norm_num⟩
  | _ => zero

def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581330113798723/10141204801825835211973625643008), (461670727435/10141204801825835211973625643008)), (19/316912650057057350374175801344), by norm_num⟩
  | 17 => ⟨((1778836112383747/633825300114114700748351602688), (34150162555/39614081257132168796771975168)), (361/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944908819415309/19807040628566084398385987584), (614593857597/39614081257132168796771975168)), (203/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((472399372640503/618970019642690137449562112), (652870710571/2475880078570760549798248448)), (863/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771263786831353/154742504910672534362390528), (652718594821/154742504910672534362390528)), (431/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549622005744797/9671406556917033397649408), (305881054671/4835703278458516698824704)), (809/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629424370521095/302231454903657293676544), (267565164137/302231454903657293676544)), (177/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((235986216397467/9444732965739290427392), (869284057067/75557863725914323419136)), (575/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648806399391591/2361183241434822606848), (651698275911/4722366482869645213696)), (863/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621549095324361/590295810358705651712), (55978444101/36893488147419103232)), (593/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1823601039174233/73786976294838206464), (559462117701/36893488147419103232)), (741/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1822799370744033/9223372036854775808), (1257904007465/9223372036854775808)), (417/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1594048187866433/1152921504606846976), (314199439403/288230376151711744)), (417/288230376151711744), by norm_num⟩
  | 5 => ⟨((597317824026909/72057594037927936), (34326712735/4503599627370496)), (365/36028797018963968), by norm_num⟩
  | 4 => ⟨((745860212711981/18014398509481984), (1645198998567/36028797018963968)), (1095/18014398509481984), by norm_num⟩
  | 3 => ⟨((372340668714379/2251799813685248), (2052160424031/9007199254740992)), (1369/4503599627370496), by norm_num⟩
  | 2 => ⟨((69630053017123/140737488355328), (3995444353/4398046511104)), (5477/4503599627370496), by norm_num⟩
  | 1 => ⟨((554108292589591/562949953421312), (6104639720423/2251799813685248)), (257/70368744177664), by norm_num⟩
  | 0 => ⟨((272678447762153/281474976710656), (12080437036801/2251799813685248)), (8239/1125899906842624), by norm_num⟩
  | _ => zero

def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((272678447762153/281474976710656), (12080437036801/2251799813685248)), (31429295066451671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1056594891352245/1125899906842624), (23405809340341/2251799813685248)), (4013/281474976710656), by norm_num⟩
  | 2 => ⟨((123929289769669/140737488355328), (43930119234703/2251799813685248)), (15231/562949953421312), by norm_num⟩
  | 3 => ⟨((1745198729310253/2251799813685248), (38683569956203/1125899906842624)), (54837/1125899906842624), by norm_num⟩
  | 4 => ⟨((1349912595237821/2251799813685248), (7495173052513/140737488355328)), (177537/2251799813685248), by norm_num⟩
  | 5 => ⟨((200715282649467/562949953421312), (287565981894727/4503599627370496)), (231771/2251799813685248), by norm_num⟩
  | 6 => ⟨((34634098174897/281474976710656), (410117361130145/9007199254740992)), (779483/9007199254740992), by norm_num⟩
  | _ => zero

def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-8723240287/4294967296), (-79436006865/4294967296)), (1/2147483648), by norm_num⟩, -3, term15ValuePoly, term15ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term15Value_checks : CertifiedScalarExp.Checks term15Value := by
  constructor
  · norm_num [term15Value, CertifiedScalarExp.reduced, term15ValuePoly, term15ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term15Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term15ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term15Value, term15ValueSquares, term15ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term15Value, CertifiedScalarExp.roundingCheck, term15ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term15 : Sound J_term15 F_term15 c := by
  apply exp_sound (A_arg15 hcre) S_arg15 term15Value term15Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term15Value,J_arg15]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term15,J_arg15,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term9Jet : Jet 12 := J_term9
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨15,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 12 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨15,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 12 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨15,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 12 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨15,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 12 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨15,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 12 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨15,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 12 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨15,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiRectangle.Tile015Terms1
