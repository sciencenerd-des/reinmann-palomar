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
namespace Reinmann.XiRectangle.Tile041Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨41,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((11/16), (17907/1280)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((11/16), (17907/1280))
  have he : value ((11/16), (17907/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_log22 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((772760613339579/250000000000000), 0), (1/125000000000000), by norm_num⟩
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

theorem S_log22 : Sound J_log22 F_log22 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log22_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog22 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1659490781/536870912), 0), (1/536870912), by norm_num⟩
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
theorem S_negLog22 : Sound J_negLog22 F_negLog22 c := by
  apply sound_round (sound_scale (A_log22 hcre) S_log22)
  intro k
  fin_cases k <;> norm_num [J_negLog22, J_log22, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg22 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-17826561/8388608), (-725500523/16777216)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1659490781/536870912), 0), (1/536870912), by norm_num⟩
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
theorem S_arg22 : Sound J_arg22 F_arg22 c := by
  apply sound_round (sound_mul (A_negLog22 hcre) (A_variable hcre) S_negLog22 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg22, J_negLog22, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term22 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((794994771595061/9007199254740992), (724584913435615/9007199254740992)), (119066101/9007199254740992), by norm_num⟩
  | 1 => ⟨((-585880897/2147483648), (-533991511/2147483648)), (45/1073741824), by norm_num⟩
  | 2 => ⟨((905491363/2147483648), (825295215/2147483648)), (141/2147483648), by norm_num⟩
  | 3 => ⟨((-233242687/536870912), (-850340849/2147483648)), (147/2147483648), by norm_num⟩
  | 4 => ⟨((720963047/2147483648), (164277479/536870912)), (115/2147483648), by norm_num⟩
  | 5 => ⟨((-445705477/2147483648), (-812461859/4294967296)), (9/268435456), by norm_num⟩
  | 6 => ⟨((459231517/4294967296), (837118033/8589934592)), (75/4294967296), by norm_num⟩
  | 7 => ⟨((-811145209/17179869184), (-739304965/17179869184)), (135/17179869184), by norm_num⟩
  | 8 => ⟨((626821069/34359738368), (285652879/17179869184)), (53/17179869184), by norm_num⟩
  | 9 => ⟨((-430562341/68719476736), (-392428967/68719476736)), (147/137438953472), by norm_num⟩
  | 10 => ⟨((266177295/137438953472), (485205839/274877906944)), (23/68719476736), by norm_num⟩
  | 11 => ⟨((-598374777/1099511627776), (-545378853/1099511627776)), (105/1099511627776), by norm_num⟩
  | 12 => ⟨((308266973/2199023255552), (561929729/4398046511104)), (55/2199023255552), by norm_num⟩
  | _ => zero

def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581207597934957/10141204801825835211973625643008), (481377655613/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778690586951787/633825300114114700748351602688), (1139275949085/633825300114114700748351602688)), (92313/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236206740276999/4951760157141521099596496896), (640723815717/19807040628566084398385987584)), (103859/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236177942384151/309485009821345068724781056), (1361242993485/2475880078570760549798248448)), (55179/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771089832457279/154742504910672534362390528), (170113888863/19342813113834066795298816)), (3449/4835703278458516698824704), by norm_num⟩
  | 13 => ⟨((387364730117629/2417851639229258349412352), (79718853201/604462909807314587353088)), (12935/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((157338254799721/75557863725914323419136), (1115711553311/604462909807314587353088)), (90555/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943828916871527/37778931862957161709568), (1812370802937/75557863725914323419136)), (73585/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324359717702939/1180591620717411303424), (1358700452665/4722366482869645213696)), (55197/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621309936487165/590295810358705651712), (1867274934333/590295810358705651712)), (75909/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1823302078946069/73786976294838206464), (2332687247029/73786976294838206464)), (189813/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455615756160245/2305843009213693952), (2622340722757/9223372036854775808)), (106797/4611686018427387904), by norm_num⟩
  | 6 => ⟨((398427955569695/288230376151711744), (1309963640645/576460752303423488)), (6677/36028797018963968), by norm_num⟩
  | 5 => ⟨((37323165834007/4503599627370496), (2289724129127/144115188075855872)), (93517/72057594037927936), by norm_num⟩
  | 4 => ⟨((1491278871529669/36028797018963968), (3429168900857/36028797018963968)), (140353/18014398509481984), by norm_num⟩
  | 3 => ⟨((186101332717857/1125899906842624), (4276997021889/9007199254740992)), (351155/9007199254740992), by norm_num⟩
  | 2 => ⟨((1113528733988777/2251799813685248), (8525666255223/4503599627370496)), (175783/1125899906842624), by norm_num⟩
  | 1 => ⟨((1107388178070723/1125899906842624), (3179476313797/562949953421312)), (1056759/2251799813685248), by norm_num⟩
  | 0 => ⟨((2178112273919555/2251799813685248), (25154782148139/2251799813685248)), (1060905/1125899906842624), by norm_num⟩
  | _ => zero

def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((2178112273919555/2251799813685248), (25154782148139/2251799813685248)), (4047031406882857921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2106555070262181/2251799813685248), (24331621048927/1125899906842624)), (4152159/2251799813685248), by norm_num⟩
  | 2 => ⟨((984813597985263/1125899906842624), (11381095996369/281474976710656)), (1987035/562949953421312), by norm_num⟩
  | 3 => ⟨((1719132131298235/2251799813685248), (159278927429793/2251799813685248)), (3636767/562949953421312), by norm_num⟩
  | 4 => ⟨((1301201594534097/2251799813685248), (121601183337495/1125899906842624)), (1516863/140737488355328), by norm_num⟩
  | 5 => ⟨((90704010883389/281474976710656), (281068774754057/2251799813685248)), (66582097/4503599627370496), by norm_num⟩
  | 6 => ⟨((794994771595061/9007199254740992), (724584913435615/9007199254740992)), (119066101/9007199254740992), by norm_num⟩
  | _ => zero

def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-17826561/8388608), (-725500523/16777216)), (1/16777216), by norm_num⟩, -7, term22ValuePoly, term22ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term22Value_checks : CertifiedScalarExp.Checks term22Value := by
  constructor
  · norm_num [term22Value, CertifiedScalarExp.reduced, term22ValuePoly, term22ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term22Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term22ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term22Value, term22ValueSquares, term22ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term22Value, CertifiedScalarExp.roundingCheck, term22ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term22 : Sound J_term22 F_term22 c := by
  apply exp_sound (A_arg22 hcre) S_arg22 term22Value term22Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term22Value,J_arg22]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term22,J_arg22,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log23 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((62709884318583/20000000000000), 0), (1/125000000000000), by norm_num⟩
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

theorem S_log23 : Sound J_log23 F_log23 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log23_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog23 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1683355639/536870912), 0), (1/536870912), by norm_num⟩
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
theorem S_negLog23 : Sound J_negLog23 F_negLog23 c := by
  apply sound_round (sound_scale (A_log23 hcre) S_log23)
  intro k
  fin_cases k <;> norm_num [J_negLog23, J_log23, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg23 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-9041461/4194304), (-5749483/131072)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1683355639/536870912), 0), (1/536870912), by norm_num⟩
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
theorem S_arg23 : Sound J_arg23 F_arg23 c := by
  apply sound_round (sound_mul (A_negLog23 hcre) (A_variable hcre) S_negLog23 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg23, J_negLog23, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term23 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1036122605732759/9007199254740992), (61008396037839/4503599627370496)), (18001793/2251799813685248), by norm_num⟩
  | 1 => ⟨((-1549127787/4294967296), (-182429765/4294967296)), (55/2147483648), by norm_num⟩
  | 2 => ⟨((75895019/134217728), (35750467/536870912)), (11/268435456), by norm_num⟩
  | 3 => ⟨((-1269164763/2147483648), (-74730255/1073741824)), (93/2147483648), by norm_num⟩
  | 4 => ⟨((994864693/2147483648), (117158141/2147483648)), (37/1073741824), by norm_num⟩
  | 5 => ⟨((-311939249/1073741824), (-146939469/4294967296)), (95/4294967296), by norm_num⟩
  | 6 => ⟨((652055807/4294967296), (9598497/536870912)), (101/8589934592), by norm_num⟩
  | 7 => ⟨((-1168295549/17179869184), (-34395465/4294967296)), (23/4294967296), by norm_num⟩
  | 8 => ⟨((57237249/2147483648), (215693563/68719476736)), (73/34359738368), by norm_num⟩
  | 9 => ⟨((-1276210227/137438953472), (-37572551/34359738368)), (13/17179869184), by norm_num⟩
  | 10 => ⟨((800309957/274877906944), (94246813/274877906944)), (33/137438953472), by norm_num⟩
  | 11 => ⟨((-1824994357/2199023255552), (-214916609/2199023255552)), (153/2199023255552), by norm_num⟩
  | 12 => ⟨((953709875/4398046511104), (224623261/8796093022208)), (81/4398046511104), by norm_num⟩
  | _ => zero

def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581167789324833/10141204801825835211973625643008), (152696035801/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778644158055161/633825300114114700748351602688), (11292728297/39614081257132168796771975168)), (46109/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889601737708855/39614081257132168796771975168), (203230956783/39614081257132168796771975168)), (103747/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944684077544301/1237940039285380274899124224), (215885424933/2475880078570760549798248448)), (13779/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1771034518229181/154742504910672534362390528), (215832046137/154742504910672534362390528)), (55117/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((48418973045453/302231454903657293676544), (25285730869/1208925819614629174706176)), (51673/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258660802282639/604462909807314587353088), (22117930099/75557863725914323419136)), (45215/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((471896115936711/18889465931478580854784), (71856717435/18889465931478580854784)), (73475/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297383964565267/4722366482869645213696), (215477253055/4722366482869645213696)), (13777/590295810358705651712), by norm_num⟩
  | 9 => ⟨((405308659309005/147573952589676412928), (148065172627/295147905179352825856)), (151551/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911604124899315/36893488147419103232), (369936761201/73786976294838206464)), (189445/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822357871808077/9223372036854775808), (207934054731/4611686018427387904)), (213135/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398401793704005/288230376151711744), (207740015797/576460752303423488)), (106573/576460752303423488), by norm_num⟩
  | 5 => ⟨((597125153781891/72057594037927936), (181554464345/72057594037927936)), (46629/36028797018963968), by norm_num⟩
  | 4 => ⟨((1491143504818971/36028797018963968), (67974051907/4503599627370496)), (34975/4503599627370496), by norm_num⟩
  | 3 => ⟨((1488643427947053/9007199254740992), (678219049151/9007199254740992)), (87449/2251799813685248), by norm_num⟩
  | 2 => ⟨((278341112346097/562949953421312), (1351884632887/4503599627370496)), (699731/4503599627370496), by norm_num⟩
  | 1 => ⟨((2214298159702221/2251799813685248), (252060187399/281474976710656)), (1049957/2251799813685248), by norm_num⟩
  | 0 => ⟨((136075873838929/140737488355328), (996952436369/562949953421312)), (2101393/2251799813685248), by norm_num⟩
  | _ => zero

def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((136075873838929/140737488355328), (996952436369/562949953421312)), (8016178139693450217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((526272893961081/562949953421312), (7711444934259/2251799813685248)), (2035511/1125899906842624), by norm_num⟩
  | 2 => ⟨((491978799511435/562949953421312), (7209032379361/1125899906842624)), (7639461/2251799813685248), by norm_num⟩
  | 3 => ⟨((859863812620713/1125899906842624), (6300188984975/562949953421312)), (13450537/2251799813685248), by norm_num⟩
  | 4 => ⟨((328273855534197/562949953421312), (38492263746915/2251799813685248)), (20845747/2251799813685248), by norm_num⟩
  | 5 => ⟨((765049327563817/2251799813685248), (89784207293341/4503599627370496)), (25024299/2251799813685248), by norm_num⟩
  | 6 => ⟨((1036122605732759/9007199254740992), (61008396037839/4503599627370496)), (18001793/2251799813685248), by norm_num⟩
  | _ => zero

def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-9041461/4194304), (-5749483/131072)), (1/16777216), by norm_num⟩, -7, term23ValuePoly, term23ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term23Value_checks : CertifiedScalarExp.Checks term23Value := by
  constructor
  · norm_num [term23Value, CertifiedScalarExp.reduced, term23ValuePoly, term23ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term23Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term23ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term23Value, term23ValueSquares, term23ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term23Value, CertifiedScalarExp.roundingCheck, term23ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term23 : Sound J_term23 F_term23 c := by
  apply exp_sound (A_arg23 hcre) S_arg23 term23Value term23Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term23Value,J_arg23]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term23,J_arg23,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log24 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1589026915173973/500000000000000), 0), (1/125000000000000), by norm_num⟩
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

theorem S_log24 : Sound J_log24 F_log24 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log24_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog24 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-853102329/268435456), 0), (1/536870912), by norm_num⟩
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
theorem S_negLog24 : Sound J_negLog24 F_negLog24 c := by
  apply sound_round (sound_scale (A_log24 hcre) S_log24)
  intro k
  fin_cases k <;> norm_num [J_negLog24, J_log24, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg24 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-73313481/33554432), (-372961509/8388608)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-853102329/268435456), 0), (1/536870912), by norm_num⟩
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
theorem S_arg24 : Sound J_arg24 F_arg24 c := by
  apply sound_round (sound_mul (A_negLog24 hcre) (A_variable hcre) S_negLog24 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg24, J_negLog24, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term24 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((899552279871365/9007199254740992), (-466236996760955/9007199254740992)), (47111361/4503599627370496), by norm_num⟩
  | 1 => ⟨((-340798565/1073741824), (706542145/4294967296)), (145/4294967296), by norm_num⟩
  | 2 => ⟨((1083076185/2147483648), (-280678621/1073741824)), (117/2147483648), by norm_num⟩
  | 3 => ⟨((-1147358139/2147483648), (594674511/2147483648)), (63/1073741824), by norm_num⟩
  | 4 => ⟨((455795741/1073741824), (-236238451/1073741824)), (51/1073741824), by norm_num⟩
  | 5 => ⟨((-36213585/134217728), (600622811/4294967296)), (33/1073741824), by norm_num⟩
  | 6 => ⟨((76725815/536870912), (-318135271/4294967296)), (71/4294967296), by norm_num⟩
  | 7 => ⟨((-1114691521/17179869184), (288871719/8589934592)), (131/17179869184), by norm_num⟩
  | 8 => ⟨((442818707/17179869184), (-57378117/4294967296)), (53/17179869184), by norm_num⟩
  | 9 => ⟨((-625467417/68719476736), (648358203/137438953472)), (19/17179869184), by norm_num⟩
  | 10 => ⟨((12423557/4294967296), (-206051727/137438953472)), (49/137438953472), by norm_num⟩
  | 11 => ⟨((-918870875/1099511627776), (119062451/274877906944)), (115/1099511627776), by norm_num⟩
  | 12 => ⟨((486703517/2199023255552), (-252257919/2199023255552)), (31/1099511627776), by norm_num⟩
  | _ => zero

def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197641209410467/1267650600228229401496703205376), (-622882015069/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778598785801869/633825300114114700748351602688), (-737014302295/633825300114114700748351602688)), (92273/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944775344086211/19807040628566084398385987584), (-207245832739/9903520314283042199192993792)), (25953/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1889313906805065/2475880078570760549798248448), (-880598532377/2475880078570760549798248448)), (55153/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770980260790967/154742504910672534362390528), (-880377830583/154742504910672534362390528)), (110311/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549356261390653/9671406556917033397649408), (-825119797593/9671406556917033397649408)), (101/9444732965739290427392), by norm_num⟩
  | 12 => ⟨((629308138012007/302231454903657293676544), (-721745491051/604462909807314587353088)), (45251/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887512090410981/75557863725914323419136), (-1172397234985/75557863725914323419136)), (73539/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324332417173883/1180591620717411303424), (-439456910453/2361183241434822606848)), (110319/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810579977340293/295147905179352825856), (-1207882677659/590295810358705651712)), (75853/295147905179352825856), by norm_num⟩
  | 8 => ⟨((911557429045561/36893488147419103232), (-1508918211453/73786976294838206464)), (94829/36893488147419103232), by norm_num⟩
  | 7 => ⟨((113890797082829/576460752303423488), (-424062039099/2305843009213693952)), (106701/4611686018427387904), by norm_num⟩
  | 6 => ⟨((796750995266879/576460752303423488), (-423660896445/288230376151711744)), (213447/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597079098794029/72057594037927936), (-740505006559/72057594037927936)), (2919/2251799813685248), by norm_num⟩
  | 4 => ⟨((23296956142741/562949953421312), (-2217913808509/36028797018963968)), (140163/18014398509481984), by norm_num⟩
  | 3 => ⟨((1488470283237861/9007199254740992), (-2766101459325/9007199254740992)), (350585/9007199254740992), by norm_num⟩
  | 2 => ⟨((556595462658871/1125899906842624), (-5513375704699/4503599627370496)), (350853/2251799813685248), by norm_num⟩
  | 1 => ⟨((553443928429285/562949953421312), (-8223153314503/2251799813685248)), (263477/562949953421312), by norm_num⟩
  | 0 => ⟨((544040432890517/562949953421312), (-16259609438635/2251799813685248)), (2113253/2251799813685248), by norm_num⟩
  | _ => zero

def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((544040432890517/562949953421312), (-16259609438635/2251799813685248)), (8061420449263762717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2102946930822523/2251799813685248), (-7856724122513/562949953421312)), (4115057/2251799813685248), by norm_num⟩
  | 2 => ⟨((490873802054023/562949953421312), (-1834340888047/70368744177664)), (3900467/1125899906842624), by norm_num⟩
  | 3 => ⟨((427643239801839/562949953421312), (-102367026326963/2251799813685248)), (7005509/1125899906842624), by norm_num⟩
  | 4 => ⟨((1294777991797063/2251799813685248), (-38881401909079/562949953421312)), (22560741/2251799813685248), by norm_num⟩
  | 5 => ⟨((91718956508135/281474976710656), (-357706991011439/4503599627370496)), (29061131/2251799813685248), by norm_num⟩
  | 6 => ⟨((899552279871365/9007199254740992), (-466236996760955/9007199254740992)), (47111361/4503599627370496), by norm_num⟩
  | _ => zero

def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-73313481/33554432), (-372961509/8388608)), (1/16777216), by norm_num⟩, -7, term24ValuePoly, term24ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term24Value_checks : CertifiedScalarExp.Checks term24Value := by
  constructor
  · norm_num [term24Value, CertifiedScalarExp.reduced, term24ValuePoly, term24ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term24Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term24ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term24Value, term24ValueSquares, term24ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term24Value, CertifiedScalarExp.roundingCheck, term24ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term24 : Sound J_term24 F_term24 c := by
  apply exp_sound (A_arg24 hcre) S_arg24 term24Value term24Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term24Value,J_arg24]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term24,J_arg24,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log25 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((16094379124341/5000000000000), 0), (1/125000000000000), by norm_num⟩
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

theorem S_log25 : Sound J_log25 F_log25 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log25_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog25 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-54003775/16777216), 0), (1/536870912), by norm_num⟩
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
theorem S_negLog25 : Sound J_negLog25 F_negLog25 c := by
  apply sound_round (sound_scale (A_log25 hcre) S_log25)
  intro k
  fin_cases k <;> norm_num [J_negLog25, J_log25, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg25 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-74255191/33554432), (-377752187/8388608)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-54003775/16777216), 0), (1/536870912), by norm_num⟩
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
theorem S_arg25 : Sound J_arg25 F_arg25 c := by
  apply sound_round (sound_mul (A_negLog25 hcre) (A_variable hcre) S_negLog25 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg25, J_negLog25, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term25 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((490807628703749/9007199254740992), (-427096211815933/4503599627370496)), (32375249/2251799813685248), by norm_num⟩
  | 1 => ⟨((-753330617/4294967296), (1311082527/4294967296)), (201/4294967296), by norm_num⟩
  | 2 => ⟨((151554857/536870912), (-1055052963/2147483648)), (163/2147483648), by norm_num⟩
  | 3 => ⟨((-325224177/1073741824), (1132028159/2147483648)), (177/2147483648), by norm_num⟩
  | 4 => ⟨((523428121/2147483648), (-910964519/2147483648)), (145/2147483648), by norm_num⟩
  | 5 => ⟨((-336970025/2147483648), (1172912667/4294967296)), (47/1073741824), by norm_num⟩
  | 6 => ⟨((361554889/4294967296), (-1258486743/8589934592)), (51/2147483648), by norm_num⟩
  | 7 => ⟨((-332514369/8589934592), (1157403587/17179869184)), (95/8589934592), by norm_num⟩
  | 8 => ⟨((33447577/2147483648), (-931384607/34359738368)), (155/34359738368), by norm_num⟩
  | 9 => ⟨((-765607801/137438953472), (1332449509/137438953472)), (7/4294967296), by norm_num⟩
  | 10 => ⟨((61609911/34359738368), (-857797903/274877906944)), (73/137438953472), by norm_num⟩
  | 11 => ⟨((-576915355/1099511627776), (1004052703/1099511627776)), (173/1099511627776), by norm_num⟩
  | 12 => ⟨((619006297/4398046511104), (-1077306991/4398046511104)), (47/1099511627776), by norm_num⟩
  | _ => zero

def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581093117298863/10141204801825835211973625643008), (-341698707093/2535301200456458802993406410752)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778554420545231/633825300114114700748351602688), (-1617161269411/633825300114114700748351602688)), (11545/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((944750362215279/19807040628566084398385987584), (-1818954919093/39614081257132168796771975168)), (103915/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944630375217741/1237940039285380274899124224), (-966101659643/1237940039285380274899124224)), (110421/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442731756467501/38685626227668133590597632), (-1931712680341/154742504910672534362390528)), (110435/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549306270252939/9671406556917033397649408), (-1810459497221/9671406556917033397649408)), (103547/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629286225224237/302231454903657293676544), (-791815551589/302231454903657293676544)), (45309/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887440717754005/75557863725914323419136), (-2572424138729/75557863725914323419136)), (9205/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((1297276002765159/4722366482869645213696), (-1928464140669/4722366482869645213696)), (27621/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((810542971295267/295147905179352825856), (-1325125616977/295147905179352825856)), (9497/36893488147419103232), by norm_num⟩
  | 8 => ⟨((1823022011306317/73786976294838206464), (-3310734881825/73786976294838206464)), (189997/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822147845424495/9223372036854775808), (-116303749143/288230376151711744)), (213825/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796698257359417/576460752303423488), (-3718152122975/1152921504606846976)), (106961/576460752303423488), by norm_num⟩
  | 5 => ⟨((597032634476885/72057594037927936), (-812343388095/36028797018963968)), (46823/36028797018963968), by norm_num⟩
  | 4 => ⟨((1490864529602085/36028797018963968), (-4866051895807/36028797018963968)), (281159/36028797018963968), by norm_num⟩
  | 3 => ⟨((1488292239306171/9007199254740992), (-3034287053133/4503599627370496)), (87959/2251799813685248), by norm_num⟩
  | 2 => ⟨((556504788784613/1125899906842624), (-6047635871433/2251799813685248)), (352417/2251799813685248), by norm_num⟩
  | 1 => ⟨((2213215276619917/2251799813685248), (-9019275559229/1125899906842624)), (132521/281474976710656), by norm_num⟩
  | 0 => ⟨((135936001856685/140737488355328), (-35661678776993/2251799813685248)), (1066029/1125899906842624), by norm_num⟩
  | _ => zero

def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((135936001856685/140737488355328), (-35661678776993/2251799813685248)), (4066577915671920421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2100208440255117/2251799813685248), (-68890046129039/2251799813685248)), (2093085/1125899906842624), by norm_num⟩
  | 2 => ⟨((1956714636569843/2251799813685248), (-128504723599729/2251799813685248)), (2016213/562949953421312), by norm_num⟩
  | 3 => ⟨((846482596234923/1125899906842624), (-223329864411383/2251799813685248)), (14936485/2251799813685248), by norm_num⟩
  | 4 => ⟨((625334209875307/1125899906842624), (-335811100604639/2251799813685248)), (25422077/2251799813685248), by norm_num⟩
  | 5 => ⟨((1289104290755637/4503599627370496), (-746049157612415/4503599627370496)), (71643323/4503599627370496), by norm_num⟩
  | 6 => ⟨((490807628703749/9007199254740992), (-427096211815933/4503599627370496)), (32375249/2251799813685248), by norm_num⟩
  | _ => zero

def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-74255191/33554432), (-377752187/8388608)), (1/16777216), by norm_num⟩, -7, term25ValuePoly, term25ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term25Value_checks : CertifiedScalarExp.Checks term25Value := by
  constructor
  · norm_num [term25Value, CertifiedScalarExp.reduced, term25ValuePoly, term25ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term25Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term25ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term25Value, term25ValueSquares, term25ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term25Value, CertifiedScalarExp.roundingCheck, term25ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term25 : Sound J_term25 F_term25 c := by
  apply exp_sound (A_arg25 hcre) S_arg25 term25Value term25Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term25Value,J_arg25]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term25,J_arg25,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log26 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1629048269010741/500000000000000), 0), (1/125000000000000), by norm_num⟩
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

theorem S_log26 : Sound J_log26 F_log26 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log26_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog26 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-437294315/134217728), 0), (1/536870912), by norm_num⟩
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
theorem S_negLog26 : Sound J_negLog26 F_negLog26 c := by
  apply sound_round (sound_scale (A_log26 hcre) S_log26)
  intro k
  fin_cases k <;> norm_num [J_negLog26, J_log26, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg26 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-9394995/4194304), (-1529419785/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-437294315/134217728), 0), (1/536870912), by norm_num⟩
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
theorem S_arg26 : Sound J_arg26 F_arg26 c := by
  apply sound_round (sound_mul (A_negLog26 hcre) (A_variable hcre) S_negLog26 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg26, J_negLog26, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term26 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-13024773818169/4503599627370496), (-1917190629417381/18014398509481984)), (311766581/18014398509481984), by norm_num⟩
  | 1 => ⟨((40470095/4294967296), (744627971/2147483648)), (61/1073741824), by norm_num⟩
  | 2 => ⟨((-32963869/2147483648), (-1213034907/2147483648)), (25/268435456), by norm_num⟩
  | 3 => ⟨((17899911/1073741824), (2573037/4194304)), (219/2147483648), by norm_num⟩
  | 4 => ⟨((-29159819/2147483648), (-1073049977/2147483648)), (45/536870912), by norm_num⟩
  | 5 => ⟨((19001101/2147483648), (699220083/2147483648)), (59/1073741824), by norm_num⟩
  | 6 => ⟨((-20635807/4294967296), (-1518751021/8589934592)), (129/4294967296), by norm_num⟩
  | 7 => ⟨((38419115/17179869184), (1413782127/17179869184)), (121/8589934592), by norm_num⟩
  | 8 => ⟨((-1955831/2147483648), (-71972479/2147483648)), (199/34359738368), by norm_num⟩
  | 9 => ⟨((45314035/137438953472), (833753901/68719476736)), (145/68719476736), by norm_num⟩
  | 10 => ⟨((-7381875/68719476736), (-135822535/34359738368)), (191/274877906944), by norm_num⟩
  | 11 => ⟨((34983071/1099511627776), (321834859/274877906944)), (57/274877906944), by norm_num⟩
  | 12 => ⟨((-37992741/4398046511104), (-1398092053/4398046511104)), (125/2199023255552), by norm_num⟩
  | _ => zero

def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581057993395097/10141204801825835211973625643008), (-260190872185/1267650600228229401496703205376)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778511015927541/633825300114114700748351602688), (-2462706843637/633825300114114700748351602688)), (92443/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944725900018559/19807040628566084398385987584), (-2770000857259/39614081257132168796771975168)), (52007/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889208643889113/2475880078570760549798248448), (-1471226550321/1237940039285380274899124224)), (27633/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((110679673720817/9671406556917033397649408), (-1470848211567/77371252455336267181195264)), (110553/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774628570446153/4835703278458516698824704), (-1378518328003/4835703278458516698824704)), (103665/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258529313959391/604462909807314587353088), (-1205801795541/302231454903657293676544)), (90729/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887370343156957/75557863725914323419136), (-1958674926309/37778931862957161709568)), (73737/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((81076436187353/295147905179352825856), (-1468347600929/2361183241434822606848)), (110641/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405253160202541/147573952589676412928), (-4035816498761/590295810358705651712)), (152189/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822929793773553/73786976294838206464), (-1260390828165/18446744073709551616)), (95161/36893488147419103232), by norm_num⟩
  | 7 => ⟨((113877705649729/576460752303423488), (-5667351589785/9223372036854775808)), (26779/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1593290948859029/1152921504606846976), (-5661847039323/1152921504606846976)), (53595/288230376151711744), by norm_num⟩
  | 5 => ⟨((1193971764455777/144115188075855872), (-4947929546109/144115188075855872)), (93875/72057594037927936), by norm_num⟩
  | 4 => ⟨((745361005568563/18014398509481984), (-7409536096117/36028797018963968)), (281961/36028797018963968), by norm_num⟩
  | 3 => ⟨((93006884311741/562949953421312), (-9240326956529/9007199254740992)), (353039/9007199254740992), by norm_num⟩
  | 2 => ⟨((2225643210701931/4503599627370496), (-4604002293177/1125899906842624)), (707845/4503599627370496), by norm_num⟩
  | 1 => ⟨((1106311084955273/1125899906842624), (-27462872831461/2251799813685248)), (1066197/2251799813685248), by norm_num⟩
  | 0 => ⟨((2173674366795349/2251799813685248), (-27142000932721/1125899906842624)), (537545/562949953421312), by norm_num⟩
  | _ => zero

def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((2173674366795349/2251799813685248), (-27142000932721/1125899906842624)), (2050571443797874273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1048475417598701/1125899906842624), (-52400636444175/1125899906842624)), (2127415/1125899906842624), by norm_num⟩
  | 2 => ⟨((1947872751289409/2251799813685248), (-97594428855253/1125899906842624)), (8320529/2251799813685248), by norm_num⟩
  | 3 => ⟨((1668047728849515/2251799813685248), (-337688150588633/2251799813685248)), (15837471/2251799813685248), by norm_num⟩
  | 4 => ⟨((1184985415868335/2251799813685248), (-500293098192339/2251799813685248)), (28213685/2251799813685248), by norm_num⟩
  | 5 => ⟨((128108329691319/562949953421312), (-1053095433110063/4503599627370496)), (42231035/2251799813685248), by norm_num⟩
  | 6 => ⟨((-13024773818169/4503599627370496), (-1917190629417381/18014398509481984)), (311766581/18014398509481984), by norm_num⟩
  | _ => zero

def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-9394995/4194304), (-1529419785/33554432)), (1/16777216), by norm_num⟩, -7, term26ValuePoly, term26ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term26Value_checks : CertifiedScalarExp.Checks term26Value := by
  constructor
  · norm_num [term26Value, CertifiedScalarExp.reduced, term26ValuePoly, term26ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term26Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term26ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term26Value, term26ValueSquares, term26ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term26Value, CertifiedScalarExp.roundingCheck, term26ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term26 : Sound J_term26 F_term26 c := by
  apply exp_sound (A_arg26 hcre) S_arg26 term26Value term26Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term26Value,J_arg26]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term26,J_arg26,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log27 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3295836866004329/1000000000000000), 0), (1/125000000000000), by norm_num⟩
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

theorem S_log27 : Sound J_log27 F_log27 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log27_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog27 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-55294967/16777216), 0), (1/536870912), by norm_num⟩
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
theorem S_negLog27 : Sound J_negLog27 F_negLog27 c := by
  apply sound_round (sound_scale (A_log27 hcre) S_log27)
  intro k
  fin_cases k <;> norm_num [J_negLog27, J_log27, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg27 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-19007645/8388608), (-1547135897/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-55294967/16777216), 0), (1/536870912), by norm_num⟩
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
theorem S_arg27 : Sound J_arg27 F_arg27 c := by
  apply sound_round (sound_mul (A_negLog27 hcre) (A_variable hcre) S_negLog27 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg27, J_negLog27, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term27 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-492487973003385/9007199254740992), (-794063114743445/9007199254740992)), (168311519/9007199254740992), by norm_num⟩
  | 1 => ⟨((386991505/2147483648), (1247931713/4294967296)), (133/2147483648), by norm_num⟩
  | 2 => ⟨((-318865217/1073741824), (-257061209/536870912)), (111/1073741824), by norm_num⟩
  | 3 => ⟨((175154623/536870912), (1129642413/2147483648)), (123/1073741824), by norm_num⟩
  | 4 => ⟨((-72160133/268435456), (-465389639/1073741824)), (205/2147483648), by norm_num⟩
  | 5 => ⟨((761049685/4294967296), (1227078663/4294967296)), (17/268435456), by norm_num⟩
  | 6 => ⟨((-104512317/1073741824), (-674041849/4294967296)), (151/4294967296), by norm_num⟩
  | 7 => ⟨((787326965/17179869184), (1269446843/17179869184)), (143/8589934592), by norm_num⟩
  | 8 => ⟨((-648725309/34359738368), (-522986213/17179869184)), (237/34359738368), by norm_num⟩
  | 9 => ⟨((475131731/68719476736), (383039387/34359738368)), (175/68719476736), by norm_num⟩
  | 10 => ⟨((-313191335/137438953472), (-504974133/137438953472)), (29/34359738368), by norm_num⟩
  | 11 => ⟨((23459717/34359738368), (37825281/34359738368)), (35/137438953472), by norm_num⟩
  | 12 => ⟨((-206185067/1099511627776), (-83110637/274877906944)), (39/549755813888), by norm_num⟩
  | _ => zero

def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581024195184619/10141204801825835211973625643008), (-692320386441/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778468528162817/633825300114114700748351602688), (-1638133103905/316912650057057350374175801344)), (92523/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236175483829597/4951760157141521099596496896), (-3685062249233/39614081257132168796771975168)), (104109/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889157546297397/2475880078570760549798248448), (-1957236310421/1237940039285380274899124224)), (6915/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((1770823487943677/154742504910672534362390528), (-3913453587319/154742504910672534362390528)), (110667/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387302212263767/2417851639229258349412352), (-3667780281471/9671406556917033397649408)), (103779/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258486852798777/604462909807314587353088), (-802056397305/151115727451828646838272)), (90835/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943650479124763/37778931862957161709568), (-2605669087261/37778931862957161709568)), (147661/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324292650836211/1180591620717411303424), (-488341176301/590295810358705651712)), (110793/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620940077380381/590295810358705651712), (-335554439019/36893488147419103232)), (4763/18446744073709551616), by norm_num⟩
  | 8 => ⟨((455709567575457/18446744073709551616), (-6706767995853/73786976294838206464)), (47659/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1821939202020957/9223372036854775808), (-7539176309109/9223372036854775808)), (214623/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593185457759439/1152921504606846976), (-7531759289243/1152921504606846976)), (107411/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193877885607507/144115188075855872), (-6581952225263/144115188075855872)), (188191/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490578054400749/36028797018963968), (-4928135757225/18014398509481984)), (282733/36028797018963968), by norm_num⟩
  | 3 => ⟨((743962366391257/4503599627370496), (-12291229275643/9007199254740992)), (354199/9007199254740992), by norm_num⟩
  | 2 => ⟨((2225256055337313/4503599627370496), (-24495285436281/4503599627370496)), (710747/4503599627370496), by norm_num⟩
  | 1 => ⟨((276500117024741/281474976710656), (-36525545437701/2251799813685248)), (1072009/2251799813685248), by norm_num⟩
  | 0 => ⟨((33941745774487/35184372088832), (-72184858333945/2251799813685248)), (541917/562949953421312), by norm_num⟩
  | _ => zero

def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((33941745774487/35184372088832), (-72184858333945/2251799813685248)), (2067249300243186773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1046619194267971/1125899906842624), (-34817732488621/562949953421312)), (270075/140737488355328), by norm_num⟩
  | 2 => ⟨((1937228404052043/2251799813685248), (-16183013650685/140737488355328)), (2142091/562949953421312), by norm_num⟩
  | 3 => ⟨((1636828480389841/2251799813685248), (-445513048067439/2251799813685248)), (16713271/2251799813685248), by norm_num⟩
  | 4 => ⟨((1101663470767001/2251799813685248), (-323842484145441/1125899906842624)), (15455521/1125899906842624), by norm_num⟩
  | 5 => ⟨((44085101384563/281474976710656), (-1267485441280321/4503599627370496)), (96055047/4503599627370496), by norm_num⟩
  | 6 => ⟨((-492487973003385/9007199254740992), (-794063114743445/9007199254740992)), (168311519/9007199254740992), by norm_num⟩
  | _ => zero

def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-19007645/8388608), (-1547135897/33554432)), (1/16777216), by norm_num⟩, -7, term27ValuePoly, term27ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term27Value_checks : CertifiedScalarExp.Checks term27Value := by
  constructor
  · norm_num [term27Value, CertifiedScalarExp.reduced, term27ValuePoly, term27ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term27Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term27ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term27Value, term27ValueSquares, term27ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term27Value, CertifiedScalarExp.roundingCheck, term27ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term27 : Sound J_term27 F_term27 c := by
  apply exp_sound (A_arg27 hcre) S_arg27 term27Value term27Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term27Value,J_arg27]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term27,J_arg27,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term22Jet : Jet 12 := J_term22
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨41,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 12 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨41,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 12 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨41,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 12 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨41,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 12 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨41,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 12 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨41,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiRectangle.Tile041Terms3
