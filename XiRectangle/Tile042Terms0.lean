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
namespace Reinmann.XiRectangle.Tile042Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨42,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((7/8), (3525/256)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((7/8), (3525/256))
  have he : value ((7/8), (3525/256))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-10175445/16777216), (-40031745/4194304)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((-609520684070895/1125899906842624), (146414653853909/2251799813685248)), (50112377/2251799813685248), by norm_num⟩
  | 1 => ⟨((805831039/2147483648), (-193570909/4294967296)), (69/4294967296), by norm_num⟩
  | 2 => ⟨((-1117119025/8589934592), (67086565/4294967296)), (25/4294967296), by norm_num⟩
  | 3 => ⟨((1032437203/34359738368), (-62001151/17179869184)), (3/2147483648), by norm_num⟩
  | 4 => ⟨((-1431261873/274877906944), (42975923/68719476736)), (17/68719476736), by norm_num⟩
  | 5 => ⟨((1587320211/2199023255552), (-190647295/2199023255552)), (77/2199023255552), by norm_num⟩
  | 6 => ⟨((-366748843/4398046511104), (176195513/17592186044416)), (73/17592186044416), by norm_num⟩
  | 7 => ⟨((1162107093/140737488355328), (-34894121/35184372088832)), (15/35184372088832), by norm_num⟩
  | 8 => ⟨((-805511255/1125899906842624), (193494093/2251799813685248)), (85/2251799813685248), by norm_num⟩
  | 9 => ⟨((124075079/2251799813685248), (-29804419/4503599627370496)), (27/9007199254740992), by norm_num⟩
  | 10 => ⟨((-1100829327/288230376151711744), (66108317/144115188075855872)), (31/144115188075855872), by norm_num⟩
  | 11 => ⟨((277467907/1152921504606846976), (-8331417/288230376151711744)), (1/72057594037927936), by norm_num⟩
  | 12 => ⟨((-512869593/36893488147419103232), (30799457/18446744073709551616)), (61/73786976294838206464), by norm_num⟩
  | _ => zero

def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583185728209367/10141204801825835211973625643008), (3936569070009/10141204801825835211973625643008)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((890511708508799/316912650057057350374175801344), (1167503149671/158456325028528675187087900672)), (23165/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1892277371524501/39614081257132168796771975168), (5253442581639/39614081257132168796771975168)), (6517/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1892209755211795/2475880078570760549798248448), (2790716479101/1237940039285380274899124224)), (13853/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1773874700152973/154742504910672534362390528), (697629892739/19342813113834066795298816)), (6929/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1552068301475931/9671406556917033397649408), (326987842985/604462909807314587353088)), (12997/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((315246953652993/151115727451828646838272), (2288705390789/302231454903657293676544)), (11377/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((29552547428207/1180591620717411303424), (7437506193523/75557863725914323419136)), (36995/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1300215423583007/4722366482869645213696), (5577440946083/4722366482869645213696)), (27763/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1625123881447111/590295810358705651712), (119810326903/9223372036854775808)), (38201/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1828063789547341/73786976294838206464), (2395785852379/18446744073709551616)), (2987/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1827812086581095/9223372036854775808), (10778719033975/9223372036854775808)), (26911/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1599051061120003/1152921504606846976), (1346977139423/144115188075855872)), (53893/1152921504606846976), by norm_num⟩
  | 5 => ⟨((599501048290739/72057594037927936), (4712784024413/72057594037927936)), (47235/144115188075855872), by norm_num⟩
  | 4 => ⟨((1498247985435675/36028797018963968), (14131790068163/36028797018963968)), (35505/18014398509481984), by norm_num⟩
  | 3 => ⟨((1497483468857361/9007199254740992), (17653213294807/9007199254740992)), (5565/562949953421312), by norm_num⟩
  | 2 => ⟨((1122143741058111/2251799813685248), (8817922720435/1125899906842624)), (5591/140737488355328), by norm_num⟩
  | 1 => ⟨((560083230809139/562949953421312), (3301258026797/140737488355328)), (135225/1125899906842624), by norm_num⟩
  | 0 => ⟨((1114037438611827/1125899906842624), (52643611995493/1125899906842624)), (137313/562949953421312), by norm_num⟩
  | _ => zero

def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((1114037438611827/1125899906842624), (52643611995493/1125899906842624)), (523807527782249273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1099838500047017/1125899906842624), (104177919032249/1125899906842624)), (569147/1125899906842624), by norm_num⟩
  | 2 => ⟨((266185226609879/281474976710656), (25441623520461/140737488355328)), (152159/140737488355328), by norm_num⟩
  | 3 => ⟨((242527669186377/281474976710656), (192477055012351/562949953421312)), (1371201/562949953421312), by norm_num⟩
  | 4 => ⟨((352129462615521/562949953421312), (663377072726285/1125899906842624)), (3300589/562949953421312), by norm_num⟩
  | 5 => ⟨((99318763255751/2251799813685248), (1659789547620705/2251799813685248)), (32073931/2251799813685248), by norm_num⟩
  | 6 => ⟨((-609520684070895/1125899906842624), (146414653853909/2251799813685248)), (50112377/2251799813685248), by norm_num⟩
  | _ => zero

def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-10175445/16777216), (-40031745/4194304)), (1/67108864), by norm_num⟩, -2, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-64510795/67108864), (-1015181035/67108864)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-89999088247161/281474976710656), (-472320812250373/2251799813685248)), (19131361/562949953421312), by norm_num⟩
  | 1 => ⟨((754349551/2147483648), (247429585/1073741824)), (41/1073741824), by norm_num⟩
  | 2 => ⟨((-828737687/4294967296), (-543658365/4294967296)), (23/1073741824), by norm_num⟩
  | 3 => ⟨((1213948543/17179869184), (796359681/17179869184)), (137/17179869184), by norm_num⟩
  | 4 => ⟨((-333414697/17179869184), (-218722633/17179869184)), (77/34359738368), by norm_num⟩
  | 5 => ⟨((1172139147/274877906944), (96116549/34359738368)), (69/137438953472), by norm_num⟩
  | 6 => ⟨((-429242157/549755813888), (-563172383/1099511627776)), (103/1099511627776), by norm_num⟩
  | 7 => ⟨((1077875905/8796093022208), (176773743/2199023255552)), (33/2199023255552), by norm_num⟩
  | 8 => ⟨((-1184167715/70368744177664), (-388411613/35184372088832)), (37/17592186044416), by norm_num⟩
  | 9 => ⟨((1156392181/562949953421312), (189650565/140737488355328)), (147/562949953421312), by norm_num⟩
  | 10 => ⟨((-1016341329/4503599627370496), (-166681953/1125899906842624)), (33/1125899906842624), by norm_num⟩
  | 11 => ⟨((406023663/18014398509481984), (266354679/18014398509481984)), (27/9007199254740992), by norm_num⟩
  | 12 => ⟨((-1189500229/576460752303423488), (-195080349/144115188075855872)), (161/576460752303423488), by norm_num⟩
  | _ => zero

def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395680896270333/2535301200456458802993406410752), (-833998942421/2535301200456458802993406410752)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780478604067337/633825300114114700748351602688), (-123600987717/19807040628566084398385987584)), (46295/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236458088482341/4951760157141521099596496896), (-2224616025259/19807040628566084398385987584)), (26047/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((236444886974083/309485009821345068724781056), (-4726842755693/2475880078570760549798248448)), (13841/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1773224373504807/154742504910672534362390528), (-4726318013201/154742504910672534362390528)), (55381/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387864743457391/2417851639229258349412352), (-2215182744163/4835703278458516698824704)), (51937/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157556875815871/75557863725914323419136), (-3876012029377/604462909807314587353088)), (22731/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1890497885318285/75557863725914323419136), (-1574368365141/18889465931478580854784)), (18477/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((162445892653503/590295810358705651712), (-4722189506441/4722366482869645213696)), (55459/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1624233436125961/590295810358705651712), (-3245761123623/295147905179352825856)), (38151/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1826952147402009/73786976294838206464), (-8112169462983/73786976294838206464)), (95447/73786976294838206464), by norm_num⟩
  | 7 => ⟨((57080107322617/288230376151711744), (-9123118399745/9223372036854775808)), (107473/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1597804840619537/1152921504606846976), (-4559638001441/576460752303423488)), (107591/1152921504606846976), by norm_num⟩
  | 5 => ⟨((74869649362043/9007199254740992), (-3987520469661/72057594037927936)), (23569/36028797018963968), by norm_num⟩
  | 4 => ⟨((374155474647345/9007199254740992), (-1494237891701/4503599627370496)), (70841/18014398509481984), by norm_num⟩
  | 3 => ⟨((1495460440926855/9007199254740992), (-14927210898991/9007199254740992)), (44393/2251799813685248), by norm_num⟩
  | 2 => ⟨((1120135088521431/2251799813685248), (-7452213461191/1125899906842624)), (178277/2251799813685248), by norm_num⟩
  | 1 => ⟨((279297359082607/281474976710656), (-11149784585089/562949953421312)), (134589/562949953421312), by norm_num⟩
  | 0 => ⟨((1108227287889573/1125899906842624), (-44370190266265/1125899906842624)), (545431/1125899906842624), by norm_num⟩
  | _ => zero

def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((1108227287889573/1125899906842624), (-44370190266265/1125899906842624)), (2080654148582076671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1089083497020139/1125899906842624), (-21836868145687/281474976710656)), (558365/562949953421312), by norm_num⟩
  | 2 => ⟨((1046694537723011/1125899906842624), (-168982500696817/1125899906842624)), (583425/281474976710656), by norm_num⟩
  | 3 => ⟨((473849568364243/562949953421312), (-39273708829531/140737488355328)), (5039571/1125899906842624), by norm_num⟩
  | 4 => ⟨((177506566028419/281474976710656), (-528923180153703/1125899906842624)), (5648263/562949953421312), by norm_num⟩
  | 5 => ⟨((12455456956235/70368744177664), (-83388706963485/140737488355328)), (49723159/2251799813685248), by norm_num⟩
  | 6 => ⟨((-89999088247161/281474976710656), (-472320812250373/2251799813685248)), (19131361/562949953421312), by norm_num⟩
  | _ => zero

def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-64510795/67108864), (-1015181035/67108864)), (1/33554432), by norm_num⟩, -2, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-10175445/8388608), (-40031745/2097152)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((1300847968346575/4503599627370496), (-79263493524315/1125899906842624)), (50737123/4503599627370496), by norm_num⟩
  | 1 => ⟨((-859908201/2147483648), (209584301/2147483648)), (35/2147483648), by norm_num⟩
  | 2 => ⟨((596042945/2147483648), (-290545535/4294967296)), (51/4294967296), by norm_num⟩
  | 3 => ⟨((-550860649/4294967296), (268521091/8589934592)), (49/8589934592), by norm_num⟩
  | 4 => ⟨((1527310023/34359738368), (-186124637/17179869184)), (35/17179869184), by norm_num⟩
  | 5 => ⟨((-846920509/68719476736), (51604707/17179869184)), (5/8589934592), by norm_num⟩
  | 6 => ⟨((1565441501/549755813888), (-190771505/274877906944)), (19/137438953472), by norm_num⟩
  | 7 => ⟨((-620046493/1099511627776), (151123121/1099511627776)), (31/1099511627776), by norm_num⟩
  | 8 => ⟨((859566957/8796093022208), (-419002261/17592186044416)), (11/2199023255552), by norm_num⟩
  | 9 => ⟨((-1059211401/70368744177664), (129080105/35184372088832)), (7/8796093022208), by norm_num⟩
  | 10 => ⟨((587351517/281474976710656), (-286308835/562949953421312)), (1/8796093022208), by norm_num⟩
  | 11 => ⟨((-296088035/1125899906842624), (288660599/4503599627370496)), (33/2251799813685248), by norm_num⟩
  | 12 => ⟨((273643449/9007199254740992), (-8336845/1125899906842624)), (63/36028797018963968), by norm_num⟩
  | _ => zero

def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582395689313353/10141204801825835211973625643008), (-311412243867/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((890049097318377/316912650057057350374175801344), (-369064255591/633825300114114700748351602688)), (46119/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((118202330207609/2475880078570760549798248448), (-415152470009/39614081257132168796771975168)), (51885/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236388202459405/309485009821345068724781056), (-220522450867/1237940039285380274899124224)), (55129/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772771642463713/154742504910672534362390528), (-110245872839/38685626227668133590597632)), (27565/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387758832473977/2417851639229258349412352), (-206678393287/4835703278458516698824704)), (25843/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((630042554624017/302231454903657293676544), (-180810982565/302231454903657293676544)), (11307/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1889898285130149/75557863725914323419136), (-587513428557/75557863725914323419136)), (73497/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649559369037619/2361183241434822606848), (-440528118303/4722366482869645213696)), (27563/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1623618988383311/590295810358705651712), (-605552417399/590295810358705651712)), (37901/295147905179352825856), by norm_num⟩
  | 8 => ⟨((913093622919235/36893488147419103232), (-47292499845/4611686018427387904)), (47379/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1825707259589829/9223372036854775808), (-425453464275/4611686018427387904)), (26653/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1596954085967495/1152921504606846976), (-850459570851/1152921504606846976)), (106623/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1197176071117573/144115188075855872), (-743649160579/144115188075855872)), (93307/144115188075855872), by norm_num⟩
  | 4 => ⟨((747763294499599/18014398509481984), (-1114468596253/36028797018963968)), (69993/18014398509481984), by norm_num⟩
  | 3 => ⟨((373528141305061/2251799813685248), (-695664251515/4503599627370496)), (175027/9007199254740992), by norm_num⟩
  | 2 => ⟨((1118819037809081/2251799813685248), (-2777392315147/4503599627370496)), (175093/2251799813685248), by norm_num⟩
  | 1 => ⟨((139411836056681/140737488355328), (-2076475669409/1125899906842624)), (525611/2251799813685248), by norm_num⟩
  | 0 => ⟨((1104753698761875/1125899906842624), (-4126750721575/1125899906842624)), (1052559/2251799813685248), by norm_num⟩
  | _ => zero

def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((1104753698761875/1125899906842624), (-4126750721575/1125899906842624)), (4015193947798918967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1083989524680829/1125899906842624), (-63269433075/8796093022208)), (2073297/2251799813685248), by norm_num⟩
  | 2 => ⟨((2087161917286297/2251799813685248), (-31188120686145/2251799813685248)), (4022069/2251799813685248), by norm_num⟩
  | 3 => ⟨((120883086043807/140737488355328), (-28907835133585/1125899906842624)), (3783707/1125899906842624), by norm_num⟩
  | 4 => ⟨((1659789547620701/2251799813685248), (-49659381627881/1125899906842624)), (13388289/2251799813685248), by norm_num⟩
  | 5 => ⟨((1219041368141783/2251799813685248), (-146414653853925/2251799813685248)), (20917891/2251799813685248), by norm_num⟩
  | 6 => ⟨((1300847968346575/4503599627370496), (-79263493524315/1125899906842624)), (50737123/4503599627370496), by norm_num⟩
  | _ => zero

def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-10175445/8388608), (-40031745/2097152)), (1/33554432), by norm_num⟩, -3, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-47253303/33554432), (-1487213335/67108864)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-542776147993591/2251799813685248), (93203112056121/2251799813685248)), (46152473/2251799813685248), by norm_num⟩
  | 1 => ⟨((1666192075/4294967296), (-286111111/4294967296)), (9/268435456), by norm_num⟩
  | 2 => ⟨((-335204087/1073741824), (230239035/4294967296)), (59/2147483648), by norm_num⟩
  | 3 => ⟨((1438640443/8589934592), (-247036955/8589934592)), (129/8589934592), by norm_num⟩
  | 4 => ⟨((-289425309/4294967296), (198795321/17179869184)), (53/8589934592), by norm_num⟩
  | 5 => ⟨((1490598609/68719476736), (-255958981/68719476736)), (139/68719476736), by norm_num⟩
  | 6 => ⟨((-1599350609/274877906944), (17164587/17179869184)), (151/274877906944), by norm_num⟩
  | 7 => ⟨((367722215/274877906944), (-126287255/549755813888)), (141/1099511627776), by norm_num⟩
  | 8 => ⟨((-295913037/1099511627776), (25406437/549755813888)), (115/4398046511104), by norm_num⟩
  | 9 => ⟨((1693346349/35184372088832), (-290773923/35184372088832)), (83/17592186044416), by norm_num⟩
  | 10 => ⟨((-1090134325/140737488355328), (93596515/70368744177664)), (109/140737488355328), by norm_num⟩
  | 11 => ⟨((1276002555/1125899906842624), (-109554749/562949953421312)), (65/562949953421312), by norm_num⟩
  | 12 => ⟨((-684548963/4503599627370496), (117547711/4503599627370496)), (141/9007199254740992), by norm_num⟩
  | _ => zero

def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582141353606259/10141204801825835211973625643008), (3870756885175/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779785662232815/633825300114114700748351602688), (573234658491/79228162514264337593543950336)), (23163/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472721268100577/9903520314283042199192993792), (5158435885079/39614081257132168796771975168)), (52131/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890730621200793/2475880078570760549798248448), (2740023382709/1237940039285380274899124224)), (27703/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1772395773198279/154742504910672534362390528), (5479156268941/154742504910672534362390528)), (55425/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387670506914913/2417851639229258349412352), (5135762754459/9671406556917033397649408)), (51981/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259775045458455/604462909807314587353088), (2246423027679/302231454903657293676544)), (711/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((472348174835091/18889465931478580854784), (7299100197571/75557863725914323419136)), (18495/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((324684508527477/1180591620717411303424), (684096513685/590295810358705651712)), (55519/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202886632628607/73786976294838206464), (7522537538907/590295810358705651712)), (76391/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825526150797089/73786976294838206464), (9399385016933/73786976294838206464)), (95569/73786976294838206464), by norm_num⟩
  | 7 => ⟨((912479232457521/4611686018427387904), (2642274987585/2305843009213693952)), (107625/9223372036854775808), by norm_num⟩
  | 6 => ⟨((798099485390861/576460752303423488), (5281293960115/576460752303423488)), (107763/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196508245656849/144115188075855872), (2308733987519/36028797018963968)), (94449/144115188075855872), by norm_num⟩
  | 4 => ⟨((373627669676865/9007199254740992), (13837740885841/36028797018963968)), (4437/1125899906842624), by norm_num⟩
  | 3 => ⟨((1492817937458669/9007199254740992), (4317875552833/2251799813685248)), (178025/9007199254740992), by norm_num⟩
  | 2 => ⟨((279371855675333/562949953421312), (17232964464017/2251799813685248)), (44711/562949953421312), by norm_num⟩
  | 1 => ⟨((139150653238075/140737488355328), (25753009294365/1125899906842624)), (135159/562949953421312), by norm_num⟩
  | 0 => ⟨((550104591406305/562949953421312), (25559859896371/562949953421312)), (548869/1125899906842624), by norm_num⟩
  | _ => zero

def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((550104591406305/562949953421312), (25559859896371/562949953421312)), (2093769077781295421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((536391828817485/562949953421312), (99906545505459/1125899906842624)), (280633/281474976710656), by norm_num⟩
  | 2 => ⟨((1013308067013901/1125899906842624), (190386567505067/1125899906842624)), (1169183/562949953421312), by norm_num⟩
  | 3 => ⟨((439890876430965/562949953421312), (342695196138669/1125899906842624)), (4999875/1125899906842624), by norm_num⟩
  | 4 => ⟨((583156576549983/1125899906842624), (133891555778583/281474976710656)), (21715011/2251799813685248), by norm_num⟩
  | 5 => ⟨((11821746566675/281474976710656), (554789929884617/1125899906842624)), (43153177/2251799813685248), by norm_num⟩
  | 6 => ⟨((-542776147993591/2251799813685248), (93203112056121/2251799813685248)), (46152473/2251799813685248), by norm_num⟩
  | _ => zero

def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47253303/33554432), (-1487213335/67108864)), (1/33554432), by norm_num⟩, -4, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-105212575/67108864), (-1655688955/67108864)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((210244173533057/1125899906842624), (208882300942531/2251799813685248)), (42698181/4503599627370496), by norm_num⟩
  | 1 => ⟨((-89813945/268435456), (-356928673/2147483648)), (19/1073741824), by norm_num⟩
  | 2 => ⟨((321849973/1073741824), (319765165/2147483648)), (35/2147483648), by norm_num⟩
  | 3 => ⟨((-768903649/4294967296), (-95490377/1073741824)), (43/4294967296), by norm_num⟩
  | 4 => ⟨((688845197/8589934592), (684383149/17179869184)), (79/17179869184), by norm_num⟩
  | 5 => ⟨((-246848981/8589934592), (-490499995/34359738368)), (29/17179869184), by norm_num⟩
  | 6 => ⟨((1179450665/137438953472), (585905341/137438953472)), (71/137438953472), by norm_num⟩
  | 7 => ⟨((-603797685/274877906944), (-599886539/549755813888)), (37/274877906944), by norm_num⟩
  | 8 => ⟨((270465055/549755813888), (537426193/2199023255552)), (17/549755813888), by norm_num⟩
  | 9 => ⟨((-215381477/2199023255552), (-213986327/4398046511104)), (7/1099511627776), by norm_num⟩
  | 10 => ⟨((1234917763/70368744177664), (153364811/17592186044416)), (41/35184372088832), by norm_num⟩
  | 11 => ⟨((-201152327/70368744177664), (-199849347/140737488355328)), (55/281474976710656), by norm_num⟩
  | 12 => ⟨((480555449/1125899906842624), (477442613/2251799813685248)), (67/2251799813685248), by norm_num⟩
  | _ => zero

def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790966773092659/5070602400912917605986812821504), (300286650163/5070602400912917605986812821504)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889775228487765/316912650057057350374175801344), (711341785273/633825300114114700748351602688)), (5767/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1890621142948007/39614081257132168796771975168), (800148672035/39614081257132168796771975168)), (51905/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472612762200787/618970019642690137449562112), (850021979929/2475880078570760549798248448)), (55151/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886058579818571/77371252455336267181195264), (849869037249/154742504910672534362390528)), (27577/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1550421845779683/9671406556917033397649408), (796589758681/9671406556917033397649408)), (25855/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259548404163511/604462909807314587353088), (696853617695/604462909807314587353088)), (22625/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1889026314677413/75557863725914323419136), (141510334947/9444732965739290427392)), (1149/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((162308114199565/590295810358705651712), (848795707097/4722366482869645213696)), (27579/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((101420014304417/36893488147419103232), (583330762541/295147905179352825856)), (37925/295147905179352825856), by norm_num⟩
  | 8 => ⟨((912532085025507/36893488147419103232), (1457678344621/73786976294838206464)), (11853/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1824444312846627/9223372036854775808), (1638996846943/9223372036854775808)), (53347/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1595691780841119/1152921504606846976), (1637883455511/1152921504606846976)), (26679/288230376151711744), by norm_num⟩
  | 5 => ⟨((1196072275565675/144115188075855872), (357974112571/36028797018963968)), (93401/144115188075855872), by norm_num⟩
  | 4 => ⟨((746936168788003/18014398509481984), (2145344006955/36028797018963968)), (140149/36028797018963968), by norm_num⟩
  | 3 => ⟨((1492047272109459/9007199254740992), (2677309408905/9007199254740992)), (175271/9007199254740992), by norm_num⟩
  | 2 => ⟨((139594690265447/281474976710656), (1335382317521/1125899906842624)), (350797/4503599627370496), by norm_num⟩
  | 1 => ⟨((2224423686713299/2251799813685248), (1994911947119/562949953421312)), (131709/562949953421312), by norm_num⟩
  | 0 => ⟨((2197251263213173/2251799813685248), (15829176603303/2251799813685248)), (528123/1125899906842624), by norm_num⟩
  | _ => zero

def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((2197251263213173/2251799813685248), (15829176603303/2251799813685248)), (2014629368308639171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2143912847634131/2251799813685248), (7722861969313/562949953421312)), (2076169/2251799813685248), by norm_num⟩
  | 2 => ⟨((2040771115074385/2251799813685248), (58822788405575/2251799813685248)), (4010359/2251799813685248), by norm_num⟩
  | 3 => ⟨((923991244336207/1125899906842624), (106620354755043/2251799813685248)), (7478575/2251799813685248), by norm_num⟩
  | 4 => ⟨((1511533733019287/2251799813685248), (87500028788483/1125899906842624)), (12983077/2251799813685248), by norm_num⟩
  | 5 => ⟨((250256394041335/562949953421312), (234939614703135/2251799813685248)), (19447909/2251799813685248), by norm_num⟩
  | 6 => ⟨((210244173533057/1125899906842624), (208882300942531/2251799813685248)), (42698181/4503599627370496), by norm_num⟩
  | _ => zero

def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-105212575/67108864), (-1655688955/67108864)), (1/33554432), by norm_num⟩, -4, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-57132171/33554432), (-899066531/33554432)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-74347855495065/4503599627370496), (-408581665722081/2251799813685248)), (134598557/9007199254740992), by norm_num⟩
  | 1 => ⟨((137972113/4294967296), (1516462727/4294967296)), (127/4294967296), by norm_num⟩
  | 2 => ⟨((-33560167/1073741824), (-737725053/2147483648)), (63/2147483648), by norm_num⟩
  | 3 => ⟨((43536713/2147483648), (119628889/536870912)), (165/8589934592), by norm_num⟩
  | 4 => ⟨((-169437063/17179869184), (-931148277/8589934592)), (81/8589934592), by norm_num⟩
  | 5 => ⟨((16485465/4294967296), (724772353/17179869184)), (1/268435456), by norm_num⟩
  | 6 => ⟨((-85544623/68719476736), (-1880455837/137438953472)), (21/17179869184), by norm_num⟩
  | 7 => ⟨((95121229/274877906944), (1045485171/274877906944)), (95/274877906944), by norm_num⟩
  | 8 => ⟨((-46274341/549755813888), (-1017210103/1099511627776)), (47/549755813888), by norm_num⟩
  | 9 => ⟨((80040631/4398046511104), (879733095/4398046511104)), (41/2199023255552), by norm_num⟩
  | 10 => ⟨((-124601501/35184372088832), (-1369505247/35184372088832)), (129/35184372088832), by norm_num⟩
  | 11 => ⟨((44084241/70368744177664), (969066967/140737488355328)), (23/35184372088832), by norm_num⟩
  | 12 => ⟨((-114378629/1125899906842624), (-1257144831/1125899906842624)), (121/1125899906842624), by norm_num⟩
  | _ => zero

def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581757847530181/10141204801825835211973625643008), (-2164327523129/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((222417391820847/79228162514264337593543950336), (-320367674691/79228162514264337593543950336)), (46227/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890383252653193/39614081257132168796771975168), (-2882871479705/39614081257132168796771975168)), (52013/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890198093263657/2475880078570760549798248448), (-3062518284835/2475880078570760549798248448)), (55273/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771863982515207/154742504910672534362390528), (-3061919137141/154742504910672534362390528)), (13821/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((193773032116749/1208925819614629174706176), (-1434956355165/4835703278458516698824704)), (405/75557863725914323419136), by norm_num⟩
  | 12 => ⟨((1259340278784313/604462909807314587353088), (-313817158579/75557863725914323419136)), (45371/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944343835189343/37778931862957161709568), (-1019607542867/18889465931478580854784)), (73749/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298210545212973/4722366482869645213696), (-382222390179/590295810358705651712)), (27665/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((811184923537193/295147905179352825856), (-4202751102111/590295810358705651712)), (19027/147573952589676412928), by norm_num⟩
  | 8 => ⟨((912312627989169/36893488147419103232), (-5250896984079/73786976294838206464)), (23795/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1823949248124565/9223372036854775808), (-1475941362905/2305843009213693952)), (107139/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595195110749771/1152921504606846976), (-2949700277215/576460752303423488)), (6701/72057594037927936), by norm_num⟩
  | 5 => ⟨((597817943396067/72057594037927936), (-5157067962293/144115188075855872)), (46951/72057594037927936), by norm_num⟩
  | 4 => ⟨((23331471226709/562949953421312), (-965724295431/4503599627370496)), (70513/18014398509481984), by norm_num⟩
  | 3 => ⟨((186402284452053/1125899906842624), (-2410024121363/2251799813685248)), (176587/9007199254740992), by norm_num⟩
  | 2 => ⟨((2231838313833601/4503599627370496), (-9614410370251/2251799813685248)), (44261/562949953421312), by norm_num⟩
  | 1 => ⟨((2221862028765591/2251799813685248), (-14357517806579/1125899906842624)), (33339/140737488355328), by norm_num⟩
  | 0 => ⟨((1095971689972759/1125899906842624), (-28459349697045/1125899906842624)), (1076047/2251799813685248), by norm_num⟩
  | _ => zero

def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((1095971689972759/1125899906842624), (-28459349697045/1125899906842624)), (4104793557173918967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((66632477903981/70368744177664), (-55405709501237/1125899906842624)), (2149287/2251799813685248), by norm_num⟩
  | 2 => ⟨((2013573855085121/2251799813685248), (-209855654366923/2251799813685248)), (2140937/1125899906842624), by norm_num⟩
  | 3 => ⟨((111312078282871/140737488355328), (-375308547773137/2251799813685248)), (8455855/2251799813685248), by norm_num⟩
  | 4 => ⟨((42064691445511/70368744177664), (-296838993918087/1125899906842624)), (16194491/2251799813685248), by norm_num⟩
  | 5 => ⟨((40507909014847/140737488355328), (-709771978117729/2251799813685248)), (27900557/2251799813685248), by norm_num⟩
  | 6 => ⟨((-74347855495065/4503599627370496), (-408581665722081/2251799813685248)), (134598557/9007199254740992), by norm_num⟩
  | _ => zero

def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-57132171/33554432), (-899066531/33554432)), (1/33554432), by norm_num⟩, -4, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-30526335/16777216), (-120095235/4194304)), (3/67108864), by norm_num⟩
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
  | 0 => ⟨((-1367231784860935/9007199254740992), (16013998886965/281474976710656)), (192237577/9007199254740992), by norm_num⟩
  | 1 => ⟨((677842753/2147483648), (-508120339/4294967296)), (193/4294967296), by norm_num⟩
  | 2 => ⟨((-1409534379/4294967296), (528303271/4294967296)), (51/1073741824), by norm_num⟩
  | 3 => ⟨((977014781/4294967296), (-366191923/4294967296)), (9/268435456), by norm_num⟩
  | 4 => ⟨((-1015822561/8589934592), (95184337/2147483648)), (19/1073741824), by norm_num⟩
  | 5 => ⟨((844937453/17179869184), (-316688423/17179869184)), (1/134217728), by norm_num⟩
  | 6 => ⟨((-1171332027/68719476736), (439023375/68719476736)), (45/17179869184), by norm_num⟩
  | 7 => ⟨((695918993/137438953472), (-521670539/274877906944)), (217/274877906944), by norm_num⟩
  | 8 => ⟨((-90445179/68719476736), (542391695/1099511627776)), (57/274877906944), by norm_num⟩
  | 9 => ⟨((1337425511/4398046511104), (-250638183/2199023255552)), (213/4398046511104), by norm_num⟩
  | 10 => ⟨((-1112439267/17592186044416), (52118745/2199023255552)), (45/4398046511104), by norm_num⟩
  | 11 => ⟨((210295675/17592186044416), (-78820279/17592186044416)), (69/35184372088832), by norm_num⟩
  | 12 => ⟨((-583063417/281474976710656), (437072433/562949953421312)), (97/281474976710656), by norm_num⟩
  | _ => zero

def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790802825208669/5070602400912917605986812821504), (1812578413071/5070602400912917605986812821504)), (7279/1267650600228229401496703205376), by norm_num⟩
  | 17 => ⟨((444788145870907/158456325028528675187087900672), (2145995445595/316912650057057350374175801344)), (69467/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890173052771287/39614081257132168796771975168), (1206923033857/9903520314283042199192993792)), (78171/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472493582075569/618970019642690137449562112), (5128467799627/2475880078570760549798248448)), (10385/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((885819868419607/77371252455336267181195264), (5127393275023/154742504910672534362390528)), (83107/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549973516164359/9671406556917033397649408), (4805789586015/9671406556917033397649408)), (77941/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259155370511969/604462909807314587353088), (4203924360363/604462909807314587353088)), (34113/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1888386238743083/75557863725914323419136), (6829236896163/75557863725914323419136)), (13865/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1297983635997035/4722366482869645213696), (1280013795311/1180591620717411303424)), (83237/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405514122655881/147573952589676412928), (879629175663/73786976294838206464)), (114525/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824231528429659/73786976294838206464), (8791728630403/73786976294838206464)), (143269/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455875878651245/2305843009213693952), (9884421351819/9223372036854775808)), (161333/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398686473905227/288230376151711744), (2469145268171/288230376151711744)), (161527/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195238914885087/144115188075855872), (8633190083227/144115188075855872)), (141555/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492610903646401/36028797018963968), (3233038334767/9007199254740992)), (106385/18014398509481984), by norm_num⟩
  | 3 => ⟨((1490450607993939/9007199254740992), (4033586801917/2251799813685248)), (266729/9007199254740992), by norm_num⟩
  | 2 => ⟨((1115131182034481/2251799813685248), (8044051510083/1125899906842624)), (267881/2251799813685248), by norm_num⟩
  | 1 => ⟨((1109698602961243/1125899906842624), (24016623722365/1125899906842624)), (404707/1125899906842624), by norm_num⟩
  | 0 => ⟨((1093306980885531/1125899906842624), (23785804554667/562949953421312)), (205249/281474976710656), by norm_num⟩
  | _ => zero

def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((1093306980885531/1125899906842624), (23785804554667/562949953421312)), (782962800146007449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((529823783272835/562949953421312), (92388980610267/1125899906842624)), (831919/562949953421312), by norm_num⟩
  | 2 => ⟨((494856263321333/562949953421312), (173904905550345/1125899906842624)), (1702463/562949953421312), by norm_num⟩
  | 3 => ⟨((843137088341215/1125899906842624), (152869595620141/562949953421312)), (3518991/562949953421312), by norm_num⟩
  | 4 => ⟨((1096729279261837/2251799813685248), (915818715065091/2251799813685248)), (28726429/2251799813685248), by norm_num⟩
  | 5 => ⟨((161688970269009/2251799813685248), (1784182045319651/4503599627370496)), (102697083/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1367231784860935/9007199254740992), (16013998886965/281474976710656)), (192237577/9007199254740992), by norm_num⟩
  | _ => zero

def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-30526335/16777216), (-120095235/4194304)), (3/67108864), by norm_num⟩, -5, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨42,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 12 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨42,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 12 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨42,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 12 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨42,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 12 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨42,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 12 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨42,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 12 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨42,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiRectangle.Tile042Terms0
