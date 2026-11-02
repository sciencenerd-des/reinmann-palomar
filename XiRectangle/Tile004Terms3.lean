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
namespace Reinmann.XiRectangle.Tile004Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨4,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (1269/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (1269/640))
  have he : value ((3/4), (1269/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-424829639927/137438953472), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-39827778743/17179869184), (-26323672513/4294967296)), (1/17179869184), by norm_num⟩
  | 1 => ⟨((-424829639927/137438953472), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((6845057160897/70368744177664), (68105479795553/4503599627370496)), (124115/18014398509481984), by norm_num⟩
  | 1 => ⟨((-330599410625/1099511627776), (-25697867353/549755813888)), (25/1099511627776), by norm_num⟩
  | 2 => ⟨((63868550831/137438953472), (19858299737/274877906944)), (21/549755813888), by norm_num⟩
  | 3 => ⟨((-263227202737/549755813888), (-40921898359/549755813888)), (23/549755813888), by norm_num⟩
  | 4 => ⟨((406823229269/1099511627776), (31622831275/549755813888)), (19/549755813888), by norm_num⟩
  | 5 => ⟨((-251501574537/1099511627776), (-39099005587/1099511627776)), (13/549755813888), by norm_num⟩
  | 6 => ⟨((64783503665/549755813888), (40285562051/2199023255552)), (7/549755813888), by norm_num⟩
  | 7 => ⟨((-457710994527/8796093022208), (-71156790033/8796093022208)), (13/2199023255552), by norm_num⟩
  | 8 => ⟨((353701028863/17592186044416), (54987164709/17592186044416)), (21/8796093022208), by norm_num⟩
  | 9 => ⟨((-121478321779/17592186044416), (-37770591223/35184372088832)), (31/35184372088832), by norm_num⟩
  | 10 => ⟨((300395719825/140737488355328), (46700200383/140737488355328)), (5/17592186044416), by norm_num⟩
  | 11 => ⟨((-84412356617/140737488355328), (-52491746169/562949953421312)), (47/562949953421312), by norm_num⟩
  | 12 => ⟨((86974059297/562949953421312), (13521184655/562949953421312)), (25/1125899906842624), by norm_num⟩
  | _ => zero

def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790477973085629/5070602400912917605986812821504), (6278087165/316912650057057350374175801344)), (77/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778393507091191/633825300114114700748351602688), (59414415951/158456325028528675187087900672)), (91/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((29520622023189/618970019642690137449562112), (267311103287/39614081257132168796771975168)), (51/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944534336868123/1237940039285380274899124224), (141975455277/1237940039285380274899124224)), (109/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770735112655741/154742504910672534362390528), (283875414607/154742504910672534362390528)), (109/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774563262608721/4835703278458516698824704), (266053015127/9671406556917033397649408)), (51/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314603836758205/151115727451828646838272), (116358117053/302231454903657293676544)), (89/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887185749759231/75557863725914323419136), (378013659261/75557863725914323419136)), (145/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297085060954101/4722366482869645213696), (283378868725/4722366482869645213696)), (27/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((405205964738453/147573952589676412928), (194716292997/295147905179352825856)), (149/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822695098008779/73786976294838206464), (121617729227/18446744073709551616)), (93/36893488147419103232), by norm_num⟩
  | 7 => ⟨((910890508581031/4611686018427387904), (546840395835/9223372036854775808)), (209/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398257717762879/288230376151711744), (546291704337/1152921504606846976)), (209/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193746660803535/144115188075855872), (238694352945/72057594037927936)), (183/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490389270978169/36028797018963968), (357425920957/18014398509481984)), (275/36028797018963968), by norm_num⟩
  | 3 => ⟨((743851397599373/4503599627370496), (222853584337/2251799813685248)), (171/4503599627370496), by norm_num⟩
  | 2 => ⟨((2224854096074181/4503599627370496), (1776393904481/4503599627370496)), (685/4503599627370496), by norm_num⟩
  | 1 => ⟨((1105751028652265/1125899906842624), (2648561968577/2251799813685248)), (1027/2251799813685248), by norm_num⟩
  | 0 => ⟨((2171685852119729/2251799813685248), (5233355413467/2251799813685248)), (2055/2251799813685248), by norm_num⟩
  | _ => zero

def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((2171685852119729/2251799813685248), (5233355413467/2251799813685248)), (7839211470793967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((523602500500443/562949953421312), (5047164424417/1125899906842624)), (1987/1125899906842624), by norm_num⟩
  | 2 => ⟨((1947975718956731/2251799813685248), (18777569103617/2251799813685248)), (7429/2251799813685248), by norm_num⟩
  | 3 => ⟨((1684988506297969/2251799813685248), (32488011103451/2251799813685248)), (6489/1125899906842624), by norm_num⟩
  | 4 => ⟨((39386976950645/70368744177664), (48620596705891/2251799813685248)), (9899/1125899906842624), by norm_num⟩
  | 5 => ⟨((1408830390806467/4503599627370496), (108856188591149/4503599627370496)), (46037/4503599627370496), by norm_num⟩
  | 6 => ⟨((6845057160897/70368744177664), (68105479795553/4503599627370496)), (124115/18014398509481984), by norm_num⟩
  | _ => zero

def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-39827778743/17179869184), (-26323672513/4294967296)), (1/17179869184), by norm_num⟩, -1, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-430939043655/137438953472), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-80801070685/34359738368), (-6675557207/1073741824)), (1/17179869184), by norm_num⟩
  | 1 => ⟨((-430939043655/137438953472), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((855745805927337/9007199254740992), (14159291447967/2251799813685248)), (55329/9007199254740992), by norm_num⟩
  | 1 => ⟨((-163768678271/549755813888), (-10838959091/549755813888)), (23/1099511627776), by norm_num⟩
  | 2 => ⟨((513495743469/1099511627776), (33985493537/1099511627776)), (39/1099511627776), by norm_num⟩
  | 3 => ⟨((-268343822259/549755813888), (-17760219735/549755813888)), (11/274877906944), by norm_num⟩
  | 4 => ⟨((420695251287/1099511627776), (13921766563/549755813888)), (37/1099511627776), by norm_num⟩
  | 5 => ⟨((-32977188177/137438953472), (-8730323707/549755813888)), (25/1099511627776), by norm_num⟩
  | 6 => ⟨((137866377049/1099511627776), (18249252991/2199023255552)), (7/549755813888), by norm_num⟩
  | 7 => ⟨((-247016701605/4398046511104), (-16348693485/4398046511104)), (53/8796093022208), by norm_num⟩
  | 8 => ⟨((48407464945/2199023255552), (12815308465/8796093022208)), (43/17592186044416), by norm_num⟩
  | 9 => ⟨((-134916734527/17592186044416), (-17858811363/35184372088832)), (31/35184372088832), by norm_num⟩
  | 10 => ⟨((338424512593/140737488355328), (22398479893/140737488355328)), (41/140737488355328), by norm_num⟩
  | 11 => ⟨((-192932382139/281474976710656), (-12769146209/281474976710656)), (3/35184372088832), by norm_num⟩
  | 12 => ⟨((100823061377/562949953421312), (834116335/70368744177664)), (13/562949953421312), by norm_num⟩
  | _ => zero

def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395228129658349/2535301200456458802993406410752), (21521809013/2535301200456458802993406410752)), (77/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222292769955141/79228162514264337593543950336), (12729149169/79228162514264337593543950336)), (91/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944631028340043/19807040628566084398385987584), (14317373969/4951760157141521099596496896)), (51/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889007327811531/2475880078570760549798248448), (121668498727/2475880078570760549798248448)), (27/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((442668446301255/38685626227668133590597632), (60817842887/77371252455336267181195264)), (109/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549069050353247/9671406556917033397649408), (113998604177/9671406556917033397649408)), (51/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258365076138767/604462909807314587353088), (49856970757/302231454903657293676544)), (89/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943552048155279/37778931862957161709568), (161969865263/75557863725914323419136)), (9/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((1297023853008943/4722366482869645213696), (121420300387/4722366482869645213696)), (27/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((405184937556039/147573952589676412928), (166860183947/590295810358705651712)), (149/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911295020164171/36893488147419103232), (208436234367/73786976294838206464)), (93/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1821662934741403/9223372036854775808), (234299803983/9223372036854775808)), (209/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592912922820303/1152921504606846976), (234061342991/1152921504606846976)), (209/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298410901715327/36028797018963968), (102267867113/72057594037927936)), (183/144115188075855872), by norm_num⟩
  | 4 => ⟨((745117495539065/18014398509481984), (76567134443/9007199254740992)), (137/18014398509481984), by norm_num⟩
  | 3 => ⟨((743755235479273/4503599627370496), (381901148965/9007199254740992)), (343/9007199254740992), by norm_num⟩
  | 2 => ⟨((556117754988677/1125899906842624), (190251516293/1125899906842624)), (171/1125899906842624), by norm_num⟩
  | 1 => ⟨((2210931358170271/2251799813685248), (141818016013/281474976710656)), (513/1125899906842624), by norm_num⟩
  | 0 => ⟨((2170560019248363/2251799813685248), (1120690757313/1125899906842624)), (513/562949953421312), by norm_num⟩
  | _ => zero

def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((2170560019248363/2251799813685248), (1120690757313/1125899906842624)), (1956941844749273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1046124470020695/1125899906842624), (2160517588625/1125899906842624)), (3961/2251799813685248), by norm_num⟩
  | 2 => ⟨((1943994723312111/2251799813685248), (4014869001471/1125899906842624)), (7377/2251799813685248), by norm_num⟩
  | 3 => ⟨((419558943984037/562949953421312), (13864259347061/2251799813685248)), (12791/2251799813685248), by norm_num⟩
  | 4 => ⟨((1250680937456733/2251799813685248), (20665687865935/2251799813685248)), (2403/281474976710656), by norm_num⟩
  | 5 => ⟨((1388911862554459/4503599627370496), (22956020971559/2251799813685248)), (5427/562949953421312), by norm_num⟩
  | 6 => ⟨((855745805927337/9007199254740992), (14159291447967/2251799813685248)), (55329/9007199254740992), by norm_num⟩
  | _ => zero

def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-80801070685/34359738368), (-6675557207/1073741824)), (1/17179869184), by norm_num⟩, -1, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-436788392521/137438953472), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-40948911799/17179869184), (-845770981/134217728)), (1/17179869184), by norm_num⟩
  | 1 => ⟨((-436788392521/137438953472), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((207634074605097/2251799813685248), (-15200140007405/9007199254740992)), (25585/4503599627370496), by norm_num⟩
  | 1 => ⟨((-40275406867/137438953472), (5896833883/1099511627776)), (11/549755813888), by norm_num⟩
  | 2 => ⟨((255994822125/549755813888), (-4685113877/549755813888)), (37/1099511627776), by norm_num⟩
  | 3 => ⟨((-67797110417/137438953472), (4963181367/549755813888)), (21/549755813888), by norm_num⟩
  | 4 => ⟨((430925732895/1099511627776), (-7886628777/1099511627776)), (35/1099511627776), by norm_num⟩
  | 5 => ⟨((-273901035205/1099511627776), (5012826159/1099511627776)), (3/137438953472), by norm_num⟩
  | 6 => ⟨((290157411357/2199023255552), (-331896487/137438953472)), (27/2199023255552), by norm_num⟩
  | 7 => ⟨((-131733696081/2199023255552), (4821873837/4398046511104)), (13/2199023255552), by norm_num⟩
  | 8 => ⟨((52332097177/2199023255552), (-7662087309/17592186044416)), (11/4398046511104), by norm_num⟩
  | 9 => ⟨((-295669727793/35184372088832), (2705613991/17592186044416)), (33/35184372088832), by norm_num⟩
  | 10 => ⟨((93965431093/35184372088832), (-3439434763/70368744177664)), (11/35184372088832), by norm_num⟩
  | 11 => ⟨((-217183416877/281474976710656), (7949606417/562949953421312)), (53/562949953421312), by norm_num⟩
  | 12 => ⟨((230073529965/1125899906842624), (-2105356427/562949953421312)), (29/1125899906842624), by norm_num⟩
  | _ => zero

def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580870939646181/10141204801825835211973625643008), (-23837211329/10141204801825835211973625643008)), (77/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444573245498145/158456325028528675187087900672), (-28195717837/633825300114114700748351602688)), (91/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472301685865191/9903520314283042199192993792), (-31713634351/39614081257132168796771975168)), (51/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888948572081143/2475880078570760549798248448), (-16843773813/1237940039285380274899124224)), (109/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885307522926423/77371252455336267181195264), (-33678339303/154742504910672534362390528)), (109/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774506999802989/4835703278458516698824704), (-31563662817/9671406556917033397649408)), (51/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258316924123035/604462909807314587353088), (-27608428695/604462909807314587353088)), (45/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887025881872301/75557863725914323419136), (-44845374643/75557863725914323419136)), (9/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((648482610339359/2361183241434822606848), (-33618007757/4722366482869645213696)), (109/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620659177051201/590295810358705651712), (-23099369439/295147905179352825856)), (149/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822489393233261/73786976294838206464), (-28854709407/36893488147419103232)), (93/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1821549802062645/9223372036854775808), (-64869509885/9223372036854775808)), (209/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592799909147569/1152921504606846976), (-32401297457/576460752303423488)), (209/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193544853610533/144115188075855872), (-56627084439/144115188075855872)), (183/144115188075855872), by norm_num⟩
  | 4 => ⟨((745043564103003/18014398509481984), (-84790487199/36028797018963968)), (137/18014398509481984), by norm_num⟩
  | 3 => ⟨((743663054339117/4503599627370496), (-52862943897/4503599627370496)), (171/4503599627370496), by norm_num⟩
  | 2 => ⟨((1112051845271341/2251799813685248), (-52666799763/1125899906842624)), (171/1125899906842624), by norm_num⟩
  | 1 => ⟨((552595959681557/562949953421312), (-314046642627/2251799813685248)), (513/1125899906842624), by norm_num⟩
  | 0 => ⟨((2169478800156509/2251799813685248), (-620320219049/2251799813685248)), (1025/1125899906842624), by norm_num⟩
  | _ => zero

def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((2169478800156509/2251799813685248), (-620320219049/2251799813685248)), (3910068992232921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((522541774242863/562949953421312), (-597642630733/1125899906842624)), (247/140737488355328), by norm_num⟩
  | 2 => ⟨((1940135636393597/2251799813685248), (-2218976935541/2251799813685248)), (3671/1125899906842624), by norm_num⟩
  | 3 => ⟨((1671605682205589/2251799813685248), (-238981958055/140737488355328)), (12667/2251799813685248), by norm_num⟩
  | 4 => ⟨((310224172574279/562949953421312), (-177406355841/70368744177664)), (18851/2251799813685248), by norm_num⟩
  | 5 => ⟨((1367610351741605/4503599627370496), (-12513678473213/4503599627370496)), (2609/281474976710656), by norm_num⟩
  | 6 => ⟨((207634074605097/2251799813685248), (-15200140007405/9007199254740992)), (25585/4503599627370496), by norm_num⟩
  | _ => zero

def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-40948911799/17179869184), (-845770981/134217728)), (1/17179869184), by norm_num⟩, -1, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-221199462363/68719476736), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-41474899193/17179869184), (-219298529483/34359738368)), (1/17179869184), by norm_num⟩
  | 1 => ⟨((-221199462363/68719476736), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((801664347978925/9007199254740992), (-159641855446181/18014398509481984)), (53683/9007199254740992), by norm_num⟩
  | 1 => ⟨((-314997313155/1099511627776), (31363971505/1099511627776)), (23/1099511627776), by norm_num⟩
  | 2 => ⟨((253484309053/549755813888), (-6309795603/137438953472)), (5/137438953472), by norm_num⟩
  | 3 => ⟨((-271978171465/549755813888), (27080598035/549755813888)), (23/549755813888), by norm_num⟩
  | 4 => ⟨((218865990255/549755813888), (-43584541169/1099511627776)), (39/1099511627776), by norm_num⟩
  | 5 => ⟨((-281800977967/1099511627776), (28058645181/1099511627776)), (27/1099511627776), by norm_num⟩
  | 6 => ⟨((151180392567/1099511627776), (-7526441221/549755813888)), (15/1099511627776), by norm_num⟩
  | 7 => ⟨((-278074806187/4398046511104), (27687633935/4398046511104)), (15/2199023255552), by norm_num⟩
  | 8 => ⟨((223772067785/8796093022208), (-44561527761/17592186044416)), (25/8796093022208), by norm_num⟩
  | 9 => ⟨((-160065444283/17592186044416), (7968779135/8796093022208)), (37/35184372088832), by norm_num⟩
  | 10 => ⟨((412184631199/140737488355328), (-20520408409/70368744177664)), (25/70368744177664), by norm_num⟩
  | 11 => ⟨((-241231117227/281474976710656), (12009572099/140737488355328)), (61/562949953421312), by norm_num⟩
  | 12 => ⟨((32353875477/140737488355328), (-25771547531/1125899906842624)), (17/562949953421312), by norm_num⟩
  | _ => zero

def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580831058241955/10141204801825835211973625643008), (-129273673799/10141204801825835211973625643008)), (77/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889122898788383/316912650057057350374175801344), (-19112867857/79228162514264337593543950336)), (91/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889153671343989/39614081257132168796771975168), (-171979868521/39614081257132168796771975168)), (103/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((118055762241075/154742504910672534362390528), (-182683633183/2475880078570760549798248448)), (109/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885279342067769/77371252455336267181195264), (-182633057113/154742504910672534362390528)), (109/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548961175904049/9671406556917033397649408), (-85582386891/4835703278458516698824704)), (51/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314567679696495/151115727451828646838272), (-9357217631/37778931862957161709568)), (89/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((235868853383253/9444732965739290427392), (-60796756927/18889465931478580854784)), (145/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296908954819589/4722366482869645213696), (-182302266253/4722366482869645213696)), (109/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((101286365780965/36893488147419103232), (-250522697435/590295810358705651712)), (149/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455598199749557/18446744073709551616), (-312939148903/73786976294838206464)), (93/36893488147419103232), by norm_num⟩
  | 7 => ⟨((910720608994235/4611686018427387904), (-351762237875/9223372036854775808)), (209/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592691430523571/1152921504606846976), (-351394734461/1152921504606846976)), (209/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193450053308463/144115188075855872), (-307057469629/144115188075855872)), (183/144115188075855872), by norm_num⟩
  | 4 => ⟨((186243145549673/4503599627370496), (-229880826207/18014398509481984)), (137/18014398509481984), by norm_num⟩
  | 3 => ⟨((92946816704619/562949953421312), (-573262006143/9007199254740992)), (171/4503599627370496), by norm_num⟩
  | 2 => ⟨((2223750844723691/4503599627370496), (-571107718293/2251799813685248)), (171/1125899906842624), by norm_num⟩
  | 1 => ⟨((2209857651719667/2251799813685248), (-1702592215041/2251799813685248)), (513/1125899906842624), by norm_num⟩
  | 0 => ⟨((271054836091241/281474976710656), (-3362502796985/2251799813685248)), (2053/2251799813685248), by norm_num⟩
  | _ => zero

def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((271054836091241/281474976710656), (-3362502796985/2251799813685248)), (7831582076262717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1044079276447831/1125899906842624), (-3238023696259/1125899906842624)), (3961/2251799813685248), by norm_num⟩
  | 2 => ⟨((1936390693498369/2251799813685248), (-6005424491759/1125899906842624)), (3685/1125899906842624), by norm_num⟩
  | 3 => ⟨((832548398526931/1125899906842624), (-20656983850297/2251799813685248)), (12755/2251799813685248), by norm_num⟩
  | 4 => ⟨((615534430665141/1125899906842624), (-30549676251755/2251799813685248)), (19099/2251799813685248), by norm_num⟩
  | 5 => ⟨((1345232599641433/4503599627370496), (-66806569444923/4503599627370496)), (10701/1125899906842624), by norm_num⟩
  | 6 => ⟨((801664347978925/9007199254740992), (-159641855446181/18014398509481984)), (53683/9007199254740992), by norm_num⟩
  | _ => zero

def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-41474899193/17179869184), (-219298529483/34359738368)), (1/17179869184), by norm_num⟩, -1, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-6996709039/2147483648), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-20990127117/8589934592), (-110985297131/17179869184)), (1/34359738368), by norm_num⟩
  | 1 => ⟨((-6996709039/2147483648), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((385026142947929/4503599627370496), (-275496065239015/18014398509481984)), (56013/18014398509481984), by norm_num⟩
  | 1 => ⟨((-306262779147/1099511627776), (13696178839/274877906944)), (13/1099511627776), by norm_num⟩
  | 2 => ⟨((62364606279/137438953472), (-44623472859/549755813888)), (3/137438953472), by norm_num⟩
  | 3 => ⟨((-270919877083/549755813888), (48462527479/549755813888)), (15/549755813888), by norm_num⟩
  | 4 => ⟨((220670778401/549755813888), (-78947796501/1099511627776)), (27/1099511627776), by norm_num⟩
  | 5 => ⟨((-71896669915/274877906944), (51443908493/1099511627776)), (19/1099511627776), by norm_num⟩
  | 6 => ⟨((78082097115/549755813888), (-27934870027/1099511627776)), (23/2199023255552), by norm_num⟩
  | 7 => ⟨((-9085678939/137438953472), (26004143807/2199023255552)), (23/4398046511104), by norm_num⟩
  | 8 => ⟨((118408076387/4398046511104), (-2647625341/549755813888)), (5/2199023255552), by norm_num⟩
  | 9 => ⟨((-21432496875/2199023255552), (61342001475/35184372088832)), (31/35184372088832), by norm_num⟩
  | 10 => ⟨((446906520765/140737488355328), (-2498227033/4398046511104)), (21/70368744177664), by norm_num⟩
  | 11 => ⟨((-132369508011/140737488355328), (47356886385/281474976710656)), (13/140737488355328), by norm_num⟩
  | 12 => ⟨((287515090527/1125899906842624), (-51431102527/1125899906842624)), (15/562949953421312), by norm_num⟩
  | _ => zero

def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580792741223529/10141204801825835211973625643008), (-230574291253/10141204801825835211973625643008)), (39/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778200450560051/633825300114114700748351602688), (-136353265729/316912650057057350374175801344)), (23/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((236137833144105/4951760157141521099596496896), (-76682500627/9903520314283042199192993792)), (13/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888838013186497/2475880078570760549798248448), (-325819433471/2475880078570760549798248448)), (55/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((55328266071675/4835703278458516698824704), (-325728132447/154742504910672534362390528)), (55/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((48403450165739/302231454903657293676544), (-305273152987/9671406556917033397649408)), (51/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258226308132379/604462909807314587353088), (-267017078377/604462909807314587353088)), (45/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886878685284791/75557863725914323419136), (-216860547065/37778931862957161709568)), (73/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296854870813267/4722366482869645213696), (-81282989007/1180591620717411303424)), (55/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202563440406723/73786976294838206464), (-446798446479/590295810358705651712)), (75/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911149970907119/36893488147419103232), (-558111351571/73786976294838206464)), (93/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821336828359853/9223372036854775808), (-627344008631/9223372036854775808)), (105/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796293567097561/576460752303423488), (-626680619987/1152921504606846976)), (105/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193358898875165/144115188075855872), (-547600176157/144115188075855872)), (23/36028797018963968), by norm_num⟩
  | 4 => ⟨((1489808642184435/36028797018963968), (-819911893035/36028797018963968)), (69/18014398509481984), by norm_num⟩
  | 3 => ⟨((371744695103269/2251799813685248), (-511145260511/4503599627370496)), (43/2251799813685248), by norm_num⟩
  | 2 => ⟨((2223411366284539/4503599627370496), (-509201044697/1125899906842624)), (343/4503599627370496), by norm_num⟩
  | 1 => ⟨((2209351163767587/2251799813685248), (-3035838013039/2251799813685248)), (257/1125899906842624), by norm_num⟩
  | 0 => ⟨((2167436580797487/2251799813685248), (-2997322409965/1125899906842624)), (257/562949953421312), by norm_num⟩
  | _ => zero

def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((2167436580797487/2251799813685248), (-2997322409965/1125899906842624)), (980379344749273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1043109020495999/1125899906842624), (-5770056642087/1125899906842624)), (1985/2251799813685248), by norm_num⟩
  | 2 => ⟨((1932752864573341/2251799813685248), (-21383066453971/2251799813685248)), (3699/2251799813685248), by norm_num⟩
  | 3 => ⟨((25917298862487/35184372088832), (-36706800214747/2251799813685248)), (6421/2251799813685248), by norm_num⟩
  | 4 => ⟨((1221228427112613/2251799813685248), (-54077481277727/2251799813685248)), (4835/1125899906842624), by norm_num⟩
  | 5 => ⟨((330507731673225/1125899906842624), (-58656153181689/2251799813685248)), (21907/4503599627370496), by norm_num⟩
  | 6 => ⟨((385026142947929/4503599627370496), (-275496065239015/18014398509481984)), (56013/18014398509481984), by norm_num⟩
  | _ => zero

def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20990127117/8589934592), (-110985297131/17179869184)), (1/34359738368), by norm_num⟩, -1, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-226488184839/68719476736), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-84933069315/34359738368), (-224541802001/34359738368)), (1/17179869184), by norm_num⟩
  | 1 => ⟨((-226488184839/68719476736), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((23014234163233/281474976710656), (-378986067923717/18014398509481984)), (7263/1125899906842624), by norm_num⟩
  | 1 => ⟨((-296293599211/1099511627776), (76237564353/1099511627776)), (25/1099511627776), by norm_num⟩
  | 2 => ⟨((61033460465/137438953472), (-3926040237/34359738368)), (11/274877906944), by norm_num⟩
  | 3 => ⟨((-268208438747/549755813888), (69011136803/549755813888)), (13/274877906944), by norm_num⟩
  | 4 => ⟨((220992815049/549755813888), (-28431181105/274877906944)), (23/549755813888), by norm_num⟩
  | 5 => ⟨((-9104453337/34359738368), (9370453483/137438953472)), (1/34359738368), by norm_num⟩
  | 6 => ⟨((80018114541/549755813888), (-82355962775/2199023255552)), (37/2199023255552), by norm_num⟩
  | 7 => ⟨((-301401887831/4398046511104), (77551948071/4398046511104)), (37/4398046511104), by norm_num⟩
  | 8 => ⟨((248342863349/8796093022208), (-63899642371/8796093022208)), (1/274877906944), by norm_num⟩
  | 9 => ⟨((-45472086913/4398046511104), (46800621567/17592186044416)), (49/35184372088832), by norm_num⟩
  | 10 => ⟨((239789728675/70368744177664), (-61698885565/70368744177664)), (17/35184372088832), by norm_num⟩
  | 11 => ⟨((-287384664675/281474976710656), (73945258777/281474976710656)), (21/140737488355328), by norm_num⟩
  | 12 => ⟨((315724324187/1125899906842624), (-81237169981/1125899906842624)), (3/70368744177664), by norm_num⟩
  | _ => zero

def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580755870480317/10141204801825835211973625643008), (-164025659305/5070602400912917605986812821504)), (77/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778156802717749/633825300114114700748351602688), (-193988573235/316912650057057350374175801344)), (91/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944526784751161/19807040628566084398385987584), (-109095254393/9903520314283042199192993792)), (103/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888785859122137/2475880078570760549798248448), (-3621390469/19342813113834066795298816)), (109/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221306546443551/19342813113834066795298816), (-463406584329/154742504910672534362390528)), (109/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((48401922921985/302231454903657293676544), (-434304117421/9671406556917033397649408)), (51/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258183557327243/604462909807314587353088), (-189938303249/302231454903657293676544)), (89/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886809237756435/75557863725914323419136), (-617038055709/75557863725914323419136)), (9/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((648401402436639/2361183241434822606848), (-462549916205/4722366482869645213696)), (109/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620435964595011/590295810358705651712), (-317817426729/295147905179352825856)), (149/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822210541479369/73786976294838206464), (-793987056205/73786976294838206464)), (93/36893488147419103232), by norm_num⟩
  | 7 => ⟨((910618159463851/4611686018427387904), (-223117726011/2305843009213693952)), (105/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1592486707134101/1152921504606846976), (-891516237195/1152921504606846976)), (209/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193271117782411/144115188075855872), (-97375510245/18014398509481984)), (183/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489677155512033/36028797018963968), (-583182151765/18014398509481984)), (275/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486814745304537/9007199254740992), (-363553725945/2251799813685248)), (343/9007199254740992), by norm_num⟩
  | 2 => ⟨((2223084263926233/4503599627370496), (-2897239148429/4503599627370496)), (685/4503599627370496), by norm_num⟩
  | 1 => ⟨((2208862923456717/2251799813685248), (-4317989467579/2251799813685248)), (257/562949953421312), by norm_num⟩
  | 0 => ⟨((2166469714636727/2251799813685248), (-8525143922389/2251799813685248)), (1029/1125899906842624), by norm_num⟩
  | _ => zero

def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((2166469714636727/2251799813685248), (-8525143922389/2251799813685248)), (3925327781295421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2084340853851449/2251799813685248), (-16404181231855/2251799813685248)), (497/281474976710656), by norm_num⟩
  | 2 => ⟨((1929215763972669/2251799813685248), (-3796064031507/281474976710656)), (1855/562949953421312), by norm_num⟩
  | 3 => ⟨((826217143018281/1125899906842624), (-52036075506357/2251799813685248)), (12915/2251799813685248), by norm_num⟩
  | 4 => ⟨((1211400453955429/2251799813685248), (-76371083037589/2251799813685248)), (19553/2251799813685248), by norm_num⟩
  | 5 => ⟨((1298213552231329/4503599627370496), (-164341366578929/4503599627370496)), (44729/4503599627370496), by norm_num⟩
  | 6 => ⟨((23014234163233/281474976710656), (-378986067923717/18014398509481984)), (7263/1125899906842624), by norm_num⟩
  | _ => zero

def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-84933069315/34359738368), (-224541802001/34359738368)), (1/17179869184), by norm_num⟩, -1, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨4,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 12 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨4,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 12 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨4,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 12 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨4,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 12 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨4,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 12 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨4,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiRectangle.Tile004Terms3
