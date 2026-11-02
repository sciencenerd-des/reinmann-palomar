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
namespace Reinmann.XiRectangle.Tile007Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨7,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (423/128)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (423/128))
  have he : value ((3/4), (423/128))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-47632711549/68719476736), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-17862266831/34359738368), (-9838201653/4294967296)), (1/17179869184), by norm_num⟩
  | 1 => ⟨((-47632711549/68719476736), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-882706135551105/2251799813685248), (-503378224957363/1125899906842624)), (232215/2251799813685248), by norm_num⟩
  | 1 => ⟨((37344071601/137438953472), (42592187181/137438953472)), (3/34359738368), by norm_num⟩
  | 2 => ⟨((-25884937941/274877906944), (-59045308917/549755813888)), (19/549755813888), by norm_num⟩
  | 3 => ⟨((23922762337/1099511627776), (54569452535/2199023255552)), (5/549755813888), by norm_num⟩
  | 4 => ⟨((-16581995265/4398046511104), (-37824662169/8796093022208)), (15/8796093022208), by norm_num⟩
  | 5 => ⟨((36780042451/70368744177664), (41948892701/70368744177664)), (9/35184372088832), by norm_num⟩
  | 6 => ⟨((-4248997121/70368744177664), (-19384504469/281474976710656)), (19/562949953421312), by norm_num⟩
  | 7 => ⟨((26927363425/4503599627370496), (61423152545/9007199254740992)), (1/281474976710656), by norm_num⟩
  | 8 => ⟨((-9332313019/18014398509481984), (-2660955313/4503599627370496)), (3/9007199254740992), by norm_num⟩
  | 9 => ⟨((22999702959/576460752303423488), (52463891137/1152921504606846976)), (1/36028797018963968), by norm_num⟩
  | 10 => ⟨((-51014973631/18446744073709551616), (-14546079289/4611686018427387904)), (19/9223372036854775808), by norm_num⟩
  | 11 => ⟨((51434014747/295147905179352825856), (58662247839/295147905179352825856)), (5/36893488147419103232), by norm_num⟩
  | 12 => ⟨((-11883780769/1180591620717411303424), (-27107714463/2361183241434822606848)), (39/4722366482869645213696), by norm_num⟩
  | _ => zero

def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((24739040482979/158456325028528675187087900672), (-2983807608009/10141204801825835211973625643008)), (77/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1781162260425857/633825300114114700748351602688), (-3540241918547/633825300114114700748351602688)), (91/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((946216930584161/19807040628566084398385987584), (-3889228695/38685626227668133590597632)), (103/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1892376381764243/2475880078570760549798248448), (-4231254416647/2475880078570760549798248448)), (109/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1774041727519067/154742504910672534362390528), (-4230999587149/154742504910672534362390528)), (109/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1552225315398469/9671406556917033397649408), (-991572810035/2417851639229258349412352)), (51/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1261125627451249/604462909807314587353088), (-3470233831359/604462909807314587353088)), (45/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((472896944785653/18889465931478580854784), (-5638621565731/75557863725914323419136)), (145/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((325096169822931/1180591620717411303424), (-2114260518645/2361183241434822606848)), (55/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1625357741704815/590295810358705651712), (-2906746278759/295147905179352825856)), (75/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1828357814588479/73786976294838206464), (-7265778982285/73786976294838206464)), (187/73786976294838206464), by norm_num⟩
  | 7 => ⟨((914072600307923/4611686018427387904), (-8172505642231/9223372036854775808)), (211/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199923386638245/144115188075855872), (-4085316891193/576460752303423488)), (211/1152921504606846976), by norm_num⟩
  | 5 => ⟨((299824851169297/36028797018963968), (-7147195668987/144115188075855872)), (185/144115188075855872), by norm_num⟩
  | 4 => ⟨((1498700501313445/36028797018963968), (-2679142027323/9007199254740992)), (277/36028797018963968), by norm_num⟩
  | 3 => ⟨((187257571014619/1125899906842624), (-13388298588769/9007199254740992)), (347/9007199254740992), by norm_num⟩
  | 2 => ⟨((561368996297681/1125899906842624), (-13377147103999/2251799813685248)), (87/562949953421312), by norm_num⟩
  | 1 => ⟨((1121100616494567/1125899906842624), (-20037722612435/1125899906842624)), (525/1125899906842624), by norm_num⟩
  | 0 => ⟨((1116076236471013/1125899906842624), (-9990684743459/281474976710656)), (531/562949953421312), by norm_num⟩
  | _ => zero

def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((1116076236471013/1125899906842624), (-9990684743459/281474976710656)), (2025606395530523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((552459920081909/562949953421312), (-79228114403293/1125899906842624)), (1091/562949953421312), by norm_num⟩
  | 2 => ⟨((1078755537409869/1125899906842624), (-155503548709687/1125899906842624)), (4591/1125899906842624), by norm_num⟩
  | 3 => ⟨((1012107869363587/1125899906842624), (-297984418042781/1125899906842624)), (10067/1125899906842624), by norm_num⟩
  | 4 => ⟨((830950975433535/1125899906842624), (-16741739908223/35184372088832)), (23429/1125899906842624), by norm_num⟩
  | 5 => ⟨((358350511838209/1125899906842624), (-395390461198771/562949953421312)), (3555/70368744177664), by norm_num⟩
  | 6 => ⟨((-882706135551105/2251799813685248), (-503378224957363/1125899906842624)), (232215/2251799813685248), by norm_num⟩
  | _ => zero

def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-17862266831/34359738368), (-9838201653/4294967296)), (1/17179869184), by norm_num⟩, 0, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-75496061613/68719476736), 0), (1/68719476736), by norm_num⟩
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
  | 0 => ⟨((-55294967/67108864), (-31186361389/8589934592)), (1/8589934592), by norm_num⟩
  | 1 => ⟨((-75496061613/68719476736), 0), (1/68719476736), by norm_num⟩
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
  | 0 => ⟨((-54505188115637/140737488355328), (464014128040041/2251799813685248)), (42451/281474976710656), by norm_num⟩
  | 1 => ⟨((14619157583/34359738368), (-31113990673/137438953472)), (25/137438953472), by norm_num⟩
  | 2 => ⟨((-64243144683/274877906944), (34182212503/274877906944)), (15/137438953472), by norm_num⟩
  | 3 => ⟨((23526102737/274877906944), (-25035332473/549755813888)), (3/68719476736), by norm_num⟩
  | 4 => ⟨((-51692131143/2199023255552), (13752061953/1099511627776)), (29/2199023255552), by norm_num⟩
  | 5 => ⟨((45431688401/8796093022208), (-12086547405/4398046511104)), (27/8796093022208), by norm_num⟩
  | 6 => ⟨((-66549081563/70368744177664), (35409145351/70368744177664)), (21/35184372088832), by norm_num⟩
  | 7 => ⟨((41778079317/281474976710656), (-2778637301/35184372088832)), (55/562949953421312), by norm_num⟩
  | 8 => ⟨((-45897911335/2251799813685248), (24421160677/2251799813685248)), (1/70368744177664), by norm_num⟩
  | 9 => ⟨((5602667713/2251799813685248), (-47696688397/36028797018963968)), (65/36028797018963968), by norm_num⟩
  | 10 => ⟨((-78786042865/288230376151711744), (41920134401/288230376151711744)), (15/72057594037927936), by norm_num⟩
  | 11 => ⟨((62949319903/2305843009213693952), (-33493799851/2305843009213693952)), (25/1152921504606846976), by norm_num⟩
  | 12 => ⟨((-23052298803/9223372036854775808), (24531133407/18446744073709551616)), (19/9223372036854775808), by norm_num⟩
  | _ => zero

def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791451234115199/5070602400912917605986812821504), (3455327215837/10141204801825835211973625643008)), (153/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((890345054187053/316912650057057350374175801344), (4097640426803/633825300114114700748351602688)), (91/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1891902591257819/39614081257132168796771975168), (4609481464931/39614081257132168796771975168)), (205/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((59119118078019/77371252455336267181195264), (4897159360631/2475880078570760549798248448)), (217/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1773476979222923/154742504910672534362390528), (2448346317939/77371252455336267181195264)), (217/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1551695709879519/9671406556917033397649408), (2295076649905/4835703278458516698824704)), (51/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1260662068744901/604462909807314587353088), (4015887920935/604462909807314587353088)), (179/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1890834207967285/75557863725914323419136), (815610888075/9444732965739290427392)), (145/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324954812227445/1180591620717411303424), (611606318311/590295810358705651712)), (109/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1624579865883375/590295810358705651712), (420396550287/36893488147419103232)), (299/590295810358705651712), by norm_num⟩
  | 8 => ⟨((28552888391213/1152921504606846976), (8405942778373/73786976294838206464)), (187/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1827049782099343/9223372036854775808), (4726974947097/4611686018427387904)), (421/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1598290624938595/1152921504606846976), (9450527355263/1152921504606846976)), (421/1152921504606846976), by norm_num⟩
  | 5 => ⟨((599169408419841/72057594037927936), (8265357132987/144115188075855872)), (369/144115188075855872), by norm_num⟩
  | 4 => ⟨((1497257269841005/36028797018963968), (12390317245273/36028797018963968)), (555/36028797018963968), by norm_num⟩
  | 3 => ⟨((748126215886455/4503599627370496), (15474367152055/9007199254740992)), (695/9007199254740992), by norm_num⟩
  | 2 => ⟨((560461870374627/1125899906842624), (7727014474687/1125899906842624)), (349/1125899906842624), by norm_num⟩
  | 1 => ⟨((69897753437281/70368744177664), (23130044137469/1125899906842624)), (1053/1125899906842624), by norm_num⟩
  | 0 => ⟨((1110543008831093/1125899906842624), (1439224152973/35184372088832)), (1067/562949953421312), by norm_num⟩
  | _ => zero

def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((1110543008831093/1125899906842624), (1439224152973/35184372088832)), (4070284129905523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((273377919304977/281474976710656), (90853991493135/1125899906842624)), (4385/1125899906842624), by norm_num⟩
  | 2 => ⟨((131840465261275/140737488355328), (44120218864921/281474976710656)), (4613/562949953421312), by norm_num⟩
  | 3 => ⟨((960384332537235/1125899906842624), (82662128627653/281474976710656)), (20179/1125899906842624), by norm_num⟩
  | 4 => ⟨((722097604852681/1125899906842624), (564081497800655/1125899906842624)), (46279/1125899906842624), by norm_num⟩
  | 5 => ⟨((22563841325701/140737488355328), (45221815015269/70368744177664)), (105735/1125899906842624), by norm_num⟩
  | 6 => ⟨((-54505188115637/140737488355328), (464014128040041/2251799813685248)), (42451/281474976710656), by norm_num⟩
  | _ => zero

def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-55294967/67108864), (-31186361389/8589934592)), (1/8589934592), by norm_num⟩, -1, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-47632711549/34359738368), 0), (1/68719476736), by norm_num⟩
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
  | 0 => ⟨((-17862266831/17179869184), (-9838201653/2147483648)), (1/8589934592), by norm_num⟩
  | 1 => ⟨((-47632711549/34359738368), 0), (1/68719476736), by norm_num⟩
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
  | 0 => ⟨((-208178743315263/4503599627370496), (789297600918689/2251799813685248)), (255327/2251799813685248), by norm_num⟩
  | 1 => ⟨((4403641021/68719476736), (-8348074443/17179869184)), (23/137438953472), by norm_num⟩
  | 2 => ⟨((-1526185679/34359738368), (23145777053/68719476736)), (17/137438953472), by norm_num⟩
  | 3 => ⟨((5641980269/274877906944), (-42782480283/274877906944)), (33/549755813888), by norm_num⟩
  | 4 => ⟨((-15642890865/2199023255552), (59309111171/1099511627776)), (3/137438953472), by norm_num⟩
  | 5 => ⟨((8674260559/4398046511104), (-65775909103/4398046511104)), (7/1099511627776), by norm_num⟩
  | 6 => ⟨((-1002089875/2199023255552), (60789847925/17592186044416)), (7/4398046511104), by norm_num⟩
  | 7 => ⟨((6350589911/70368744177664), (-48155784795/70368744177664)), (23/70368744177664), by norm_num⟩
  | 8 => ⟨((-8803786983/562949953421312), (16689523229/140737488355328)), (17/281474976710656), by norm_num⟩
  | 9 => ⟨((1356071139/562949953421312), (-1285366219/70368744177664)), (11/1125899906842624), by norm_num⟩
  | 10 => ⟨((-12031448149/36028797018963968), (45616536099/18014398509481984)), (51/36028797018963968), by norm_num⟩
  | 11 => ⟨((3032568859/72057594037927936), (-45991234013/144115188075855872)), (27/144115188075855872), by norm_num⟩
  | 12 => ⟨((-11210754957/2305843009213693952), (21252462791/576460752303423488)), (13/576460752303423488), by norm_num⟩
  | _ => zero

def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582621414715929/10141204801825835211973625643008), (554233791967/2535301200456458802993406410752)), (153/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1780362135069781/633825300114114700748351602688), (657027142833/158456325028528675187087900672)), (91/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((945766985657419/19807040628566084398385987584), (2956341504135/39614081257132168796771975168)), (205/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1891420547201513/2475880078570760549798248448), (3140778826919/2475880078570760549798248448)), (217/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((55408944646711/4835703278458516698824704), (3140403044117/154742504910672534362390528)), (217/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1551329891970365/9671406556917033397649408), (1471864295911/4835703278458516698824704)), (51/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1260342488668685/604462909807314587353088), (1287681631943/302231454903657293676544)), (89/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((236289480932449/9444732965739290427392), (523027089983/9444732965739290427392)), (289/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324857828939341/1180591620717411303424), (3137507546225/4722366482869645213696)), (217/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((406011954457261/147573952589676412928), (33695379249/4611686018427387904)), (149/295147905179352825856), by norm_num⟩
  | 8 => ⟨((57085057381227/2305843009213693952), (5389664238751/73786976294838206464)), (373/73786976294838206464), by norm_num⟩
  | 7 => ⟨((913153343134985/4611686018427387904), (6061177255513/9223372036854775808)), (419/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1597551030384235/1152921504606846976), (6058433630127/1152921504606846976)), (105/288230376151711744), by norm_num⟩
  | 5 => ⟨((598847803898245/72057594037927936), (2649021521499/72057594037927936)), (23/9007199254740992), by norm_num⟩
  | 4 => ⟨((1496300321794067/36028797018963968), (7940892289861/36028797018963968)), (69/4503599627370496), by norm_num⟩
  | 3 => ⟨((747534997947937/4503599627370496), (9915315000175/9007199254740992)), (691/9007199254740992), by norm_num⟩
  | 2 => ⟨((139970237203727/281474976710656), (9899116721987/2251799813685248)), (693/2251799813685248), by norm_num⟩
  | 1 => ⟨((139584082920619/140737488355328), (14808187441461/1125899906842624)), (1043/1125899906842624), by norm_num⟩
  | 0 => ⟨((69210316395977/70368744177664), (29454473649057/1125899906842624)), (263/140737488355328), by norm_num⟩
  | _ => zero

def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((69210316395977/70368744177664), (29454473649057/1125899906842624)), (1003265917730287/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((544182394818751/562949953421312), (57939173545043/1125899906842624)), (2125/562949953421312), by norm_num⟩
  | 2 => ⟨((262274861271639/281474976710656), (14001901066845/140737488355328)), (8655/1125899906842624), by norm_num⟩
  | 3 => ⟨((483196699868775/562949953421312), (208748739387715/1125899906842624)), (4463/281474976710656), by norm_num⟩
  | 4 => ⟨((790780922397563/1125899906842624), (358350511838207/1125899906842624)), (37267/1125899906842624), by norm_num⟩
  | 5 => ⟨((882706135551167/2251799813685248), (1006756449914747/2251799813685248)), (152145/2251799813685248), by norm_num⟩
  | 6 => ⟨((-208178743315263/4503599627370496), (789297600918689/2251799813685248)), (255327/2251799813685248), by norm_num⟩
  | _ => zero

def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-17862266831/17179869184), (-9838201653/2147483648)), (1/8589934592), by norm_num⟩, -1, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-55299865591/34359738368), 0), (1/68719476736), by norm_num⟩
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
  | 0 => ⟨((-20737449597/17179869184), (-91374387285/17179869184)), (1/8589934592), by norm_num⟩
  | 1 => ⟨((-55299865591/34359738368), 0), (1/68719476736), by norm_num⟩
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
  | 0 => ⟨((767500133754969/4503599627370496), (1106823115696213/4503599627370496)), (163131/2251799813685248), by norm_num⟩
  | 1 => ⟨((-37696649569/137438953472), (-13590721777/34359738368)), (9/68719476736), by norm_num⟩
  | 2 => ⟨((15167604247/68719476736), (43746845771/137438953472)), (1/8589934592), by norm_num⟩
  | 3 => ⟨((-2034276443/17179869184), (-11734638689/68719476736)), (19/274877906944), by norm_num⟩
  | 4 => ⟨((13096166527/274877906944), (75544689579/1099511627776)), (33/1099511627776), by norm_num⟩
  | 5 => ⟨((-16861973533/1099511627776), (-48633794997/2199023255552)), (23/2199023255552), by norm_num⟩
  | 6 => ⟨((18092199655/4398046511104), (13045512249/2199023255552)), (13/4398046511104), by norm_num⟩
  | 7 => ⟨((-33278025193/35184372088832), (-47990724573/35184372088832)), (13/17592186044416), by norm_num⟩
  | 8 => ⟨((53558915397/281474976710656), (77238091573/281474976710656)), (11/70368744177664), by norm_num⟩
  | 9 => ⟨((-38310999551/1125899906842624), (-55248850161/1125899906842624)), (33/1125899906842624), by norm_num⟩
  | 10 => ⟨((49327340113/9007199254740992), (35567837627/4503599627370496)), (45/9007199254740992), by norm_num⟩
  | 11 => ⟨((-28868833199/36028797018963968), (-41632164611/36028797018963968)), (7/9007199254740992), by norm_num⟩
  | 12 => ⟨((7743765773/72057594037927936), (44669589401/288230376151711744)), (1/9007199254740992), by norm_num⟩
  | _ => zero

def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582403412673631/10141204801825835211973625643008), (1256363669117/10141204801825835211973625643008)), (153/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1780106237220545/633825300114114700748351602688), (1488969885415/633825300114114700748351602688)), (181/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891246264630615/39614081257132168796771975168), (1674910120573/39614081257132168796771975168)), (51/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1891115079016469/2475880078570760549798248448), (1779372681637/2475880078570760549798248448)), (217/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772781008131749/154742504910672534362390528), (889562989989/77371252455336267181195264)), (217/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1551044010718447/9671406556917033397649408), (208458565487/1208925819614629174706176)), (203/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((39377893922425/18889465931478580854784), (729473959511/302231454903657293676544)), (89/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((944955140093217/37778931862957161709568), (1185149567905/37778931862957161709568)), (289/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162390946421333/590295810358705651712), (1777294614569/4722366482869645213696)), (217/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1623630869458273/590295810358705651712), (2443081942985/590295810358705651712)), (297/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1826201700408837/73786976294838206464), (1526402749971/36893488147419103232)), (93/18446744073709551616), by norm_num⟩
  | 7 => ⟨((456430743970679/2305843009213693952), (3432967146587/9223372036854775808)), (419/9223372036854775808), by norm_num⟩
  | 6 => ⟨((399242280395825/288230376151711744), (1715584537361/576460752303423488)), (419/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1197188462476495/144115188075855872), (375031388989/18014398509481984)), (367/144115188075855872), by norm_num⟩
  | 4 => ⟨((1495543648817607/36028797018963968), (2248167758039/18014398509481984)), (549/36028797018963968), by norm_num⟩
  | 3 => ⟨((747065611364727/4503599627370496), (5613353013863/9007199254740992)), (43/562949953421312), by norm_num⟩
  | 2 => ⟨((139854213143741/281474976710656), (11205529410677/4503599627370496)), (1377/4503599627370496), by norm_num⟩
  | 1 => ⟨((34853335985069/35184372088832), (16755431367403/2251799813685248)), (1035/1125899906842624), by norm_num⟩
  | 0 => ⟨((552369148731103/562949953421312), (33299884110025/2251799813685248)), (4159/2251799813685248), by norm_num⟩
  | _ => zero

def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((552369148731103/562949953421312), (33299884110025/2251799813685248)), (15865334517668967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((270932051307073/281474976710656), (32674003305109/1125899906842624)), (4143/1125899906842624), by norm_num⟩
  | 2 => ⟨((521093937917595/562949953421312), (125800663964061/2251799813685248)), (16433/2251799813685248), by norm_num⟩
  | 3 => ⟨((240296475334393/281474976710656), (232894462391473/2251799813685248)), (32259/2251799813685248), by norm_num⟩
  | 4 => ⟨((202131284882549/281474976710656), (397646136019385/2251799813685248)), (61753/2251799813685248), by norm_num⟩
  | 5 => ⟨((2130872870097/4398046511104), (8923609007525/35184372088832)), (110503/2251799813685248), by norm_num⟩
  | 6 => ⟨((767500133754969/4503599627370496), (1106823115696213/4503599627370496)), (163131/2251799813685248), by norm_num⟩
  | _ => zero

def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20737449597/17179869184), (-91374387285/17179869184)), (1/8589934592), by norm_num⟩, -1, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-61564386581/34359738368), 0), (1/68719476736), by norm_num⟩
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
  | 0 => ⟨((-2885830621/2147483648), (-50862764695/8589934592)), (1/8589934592), by norm_num⟩
  | 1 => ⟨((-61564386581/34359738368), 0), (1/68719476736), by norm_num⟩
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
  | 0 => ⟨((549312701869461/2251799813685248), (104002823511249/1125899906842624)), (192873/4503599627370496), by norm_num⟩
  | 1 => ⟨((-60073012399/137438953472), (-22747563947/137438953472)), (3/34359738368), by norm_num⟩
  | 2 => ⟨((53818194405/137438953472), (1273692597/8589934592)), (3/34359738368), by norm_num⟩
  | 3 => ⟨((-64286172961/274877906944), (-24342941563/274877906944)), (1/17179869184), by norm_num⟩
  | 4 => ⟨((14398169893/137438953472), (21808348027/549755813888)), (1/34359738368), by norm_num⟩
  | 5 => ⟨((-82553783185/2199023255552), (-7815062817/549755813888)), (25/2199023255552), by norm_num⟩
  | 6 => ⟨((98611015161/8796093022208), (4667570935/1099511627776)), (1/274877906944), by norm_num⟩
  | 7 => ⟨((-25241031455/8796093022208), (-19115804391/17592186044416)), (9/8796093022208), by norm_num⟩
  | 8 => ⟨((90451714245/140737488355328), (34250923529/140737488355328)), (17/70368744177664), by norm_num⟩
  | 9 => ⟨((-72030095781/562949953421312), (-13637648125/281474976710656)), (29/562949953421312), by norm_num⟩
  | 10 => ⟨((25812121237/1125899906842624), (19548308133/2251799813685248)), (11/1125899906842624), by norm_num⟩
  | 11 => ⟨((-33635718289/9007199254740992), (-3184169655/2251799813685248)), (15/9007199254740992), by norm_num⟩
  | 12 => ⟨((80356155665/144115188075855872), (1901755377/9007199254740992)), (19/72057594037927936), by norm_num⟩
  | _ => zero

def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791112646017817/5070602400912917605986812821504), (117879901957/2535301200456458802993406410752)), (19/1267650600228229401496703205376), by norm_num⟩
  | 17 => ⟨((6952719450617/2475880078570760549798248448), (139672990365/158456325028528675187087900672)), (181/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891010036451515/39614081257132168796771975168), (157113371391/9903520314283042199192993792)), (51/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((236358024303571/309485009821345068724781056), (667640270503/2475880078570760549798248448)), (27/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1772530244835763/154742504910672534362390528), (667537290139/154742504910672534362390528)), (27/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1550809048960895/9671406556917033397649408), (312853407413/4835703278458516698824704)), (203/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314971785691731/151115727451828646838272), (273692046497/302231454903657293676544)), (89/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((472394161149105/18889465931478580854784), (889294134883/75557863725914323419136)), (9/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((649438777894705/2361183241434822606848), (166697816105/1180591620717411303424)), (217/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1623287440909725/590295810358705651712), (3580260409/2305843009213693952)), (297/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825772928721605/73786976294838206464), (572623258543/36893488147419103232)), (93/18446744073709551616), by norm_num⟩
  | 7 => ⟨((456310328492685/2305843009213693952), (1287801992159/9223372036854775808)), (209/4611686018427387904), by norm_num⟩
  | 6 => ⟨((399122085424855/288230376151711744), (321762996649/288230376151711744)), (209/576460752303423488), by norm_num⟩
  | 5 => ⟨((299192192826421/36028797018963968), (140665913455/18014398509481984)), (183/72057594037927936), by norm_num⟩
  | 4 => ⟨((1494916091883747/36028797018963968), (1686306038223/36028797018963968)), (549/36028797018963968), by norm_num⟩
  | 3 => ⟨((1493350235333591/9007199254740992), (2104937164803/9007199254740992)), (343/4503599627370496), by norm_num⟩
  | 2 => ⟨((2236115788182667/4503599627370496), (4201051097111/4503599627370496)), (685/2251799813685248), by norm_num⟩
  | 1 => ⟨((2228311868954025/2251799813685248), (6279563707547/2251799813685248)), (2057/2251799813685248), by norm_num⟩
  | 0 => ⟨((551244007146519/562949953421312), (6235673003451/1125899906842624)), (4121/2251799813685248), by norm_num⟩
  | _ => zero

def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((551244007146519/562949953421312), (6235673003451/1125899906842624)), (15720376021575217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2159056823177963/2251799813685248), (1526502201833/140737488355328)), (8117/2251799813685248), by norm_num⟩
  | 2 => ⟨((2069868646354693/2251799813685248), (46836205945961/2251799813685248)), (7871/1125899906842624), by norm_num⟩
  | 3 => ⟨((1901662197922781/2251799813685248), (86104274112269/2251799813685248)), (7399/562949953421312), by norm_num⟩
  | 4 => ⟨((1602675844919733/2251799813685248), (145431438588591/2251799813685248)), (52253/2251799813685248), by norm_num⟩
  | 5 => ⟨((1131281539805343/2251799813685248), (207016140867699/2251799813685248)), (81131/2251799813685248), by norm_num⟩
  | 6 => ⟨((549312701869461/2251799813685248), (104002823511249/1125899906842624)), (192873/4503599627370496), by norm_num⟩
  | _ => zero

def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2885830621/2147483648), (-50862764695/8589934592)), (1/8589934592), by norm_num⟩, -1, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-66860963609/34359738368), 0), (1/68719476736), by norm_num⟩
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
  | 0 => ⟨((-25072861353/17179869184), (-55238647669/8589934592)), (1/8589934592), by norm_num⟩
  | 1 => ⟨((-66860963609/34359738368), 0), (1/68719476736), by norm_num⟩
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
  | 0 => ⟨((1035138826011919/4503599627370496), (-38434026704149/1125899906842624)), (143489/4503599627370496), by norm_num⟩
  | 1 => ⟨((-61471165381/137438953472), (4564768227/68719476736)), (5/68719476736), by norm_num⟩
  | 2 => ⟨((119617364589/274877906944), (-8882628821/137438953472)), (21/274877906944), by norm_num⟩
  | 3 => ⟨((-77588214585/274877906944), (5761599191/137438953472)), (15/274877906944), by norm_num⟩
  | 4 => ⟨((1179528861/8589934592), (-11211554341/549755813888)), (1/34359738368), by norm_num⟩
  | 5 => ⟨((-14689645963/274877906944), (17453341903/2199023255552)), (27/2199023255552), by norm_num⟩
  | 6 => ⟨((38112974887/2199023255552), (-11320878381/4398046511104)), (19/4398046511104), by norm_num⟩
  | 7 => ⟨((-84759342449/17592186044416), (12588235507/17592186044416)), (23/17592186044416), by norm_num⟩
  | 8 => ⟨((82467032349/70368744177664), (-382743363/2199023255552)), (3/8796093022208), by norm_num⟩
  | 9 => ⟨((-8915190845/35184372088832), (5296243161/140737488355328)), (11/140737488355328), by norm_num⟩
  | 10 => ⟨((55514113107/1125899906842624), (-8244810655/1125899906842624)), (9/562949953421312), by norm_num⟩
  | 11 => ⟨((-39281991313/4503599627370496), (11668116895/9007199254740992)), (27/9007199254740992), by norm_num⟩
  | 12 => ⟨((25479741857/18014398509481984), (-7568369029/36028797018963968)), (37/72057594037927936), by norm_num⟩
  | _ => zero

def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582074693182059/10141204801825835211973625643008), (-192056590857/10141204801825835211973625643008)), (153/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779717894518717/633825300114114700748351602688), (-227519753103/633825300114114700748351602688)), (181/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890809499078665/39614081257132168796771975168), (-63981668271/9903520314283042199192993792)), (51/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((118165697763529/154742504910672534362390528), (-271881602801/2475880078570760549798248448)), (27/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1772317260449971/154742504910672534362390528), (-271836065711/154742504910672534362390528)), (27/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1550609424776895/9671406556917033397649408), (-254797939213/9671406556917033397649408)), (203/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629856260134615/302231454903657293676544), (-55724959133/151115727451828646838272)), (89/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((944646487125417/37778931862957161709568), (-362121584573/75557863725914323419136)), (9/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((649332441405609/2361183241434822606848), (-8484746737/147573952589676412928)), (217/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811497572575813/295147905179352825856), (-373200053767/590295810358705651712)), (297/590295810358705651712), by norm_num⟩
  | 8 => ⟨((456351938326073/18446744073709551616), (-233153473775/36893488147419103232)), (371/73786976294838206464), by norm_num⟩
  | 7 => ⟨((456207689649795/2305843009213693952), (-524329913439/9223372036854775808)), (417/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1596078119800397/1152921504606846976), (-523998365589/1152921504606846976)), (417/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196410201965937/144115188075855872), (-57265732589/18014398509481984)), (365/144115188075855872), by norm_num⟩
  | 4 => ⟨((373594746670481/9007199254740992), (-686444077517/36028797018963968)), (137/9007199254740992), by norm_num⟩
  | 3 => ⟨((186585020295759/1125899906842624), (-856753432395/9007199254740992)), (171/2251799813685248), by norm_num⟩
  | 2 => ⟨((1117389780173447/2251799813685248), (-213701025023/562949953421312)), (171/562949953421312), by norm_num⟩
  | 1 => ⟨((139144831014267/140737488355328), (-1277343877053/1125899906842624)), (513/562949953421312), by norm_num⟩
  | 0 => ⟨((2201025802302549/2251799813685248), (-5070609729727/2251799813685248)), (2053/1125899906842624), by norm_num⟩
  | _ => zero

def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((2201025802302549/2251799813685248), (-5070609729727/2251799813685248)), (7831577781295421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((537846308747819/562949953421312), (-4840113921/1099511627776)), (4023/1125899906842624), by norm_num⟩
  | 2 => ⟨((513851202768627/562949953421312), (-18941045028105/2251799813685248)), (7723/1125899906842624), by norm_num⟩
  | 3 => ⟨((1875979449206911/2251799813685248), (-17289065769053/1125899906842624)), (28459/2251799813685248), by norm_num⟩
  | 4 => ⟨((1562351690982843/2251799813685248), (-57614237076695/2251799813685248)), (24147/1125899906842624), by norm_num⟩
  | 5 => ⟨((1082522252283899/2251799813685248), (-79948226458147/2251799813685248)), (69487/2251799813685248), by norm_num⟩
  | 6 => ⟨((1035138826011919/4503599627370496), (-38434026704149/1125899906842624)), (143489/4503599627370496), by norm_num⟩
  | _ => zero

def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-25072861353/17179869184), (-55238647669/8589934592)), (1/8589934592), by norm_num⟩, -1, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-17862266831/8589934592), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-13396700123/8589934592), (-29514604959/4294967296)), (1/4294967296), by norm_num⟩
  | 1 => ⟨((-17862266831/8589934592), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((393689870774907/2251799813685248), (-131433794701165/1125899906842624)), (184123/2251799813685248), by norm_num⟩
  | 1 => ⟨((-195182579/536870912), (33362901939/137438953472)), (25/137438953472), by norm_num⟩
  | 2 => ⟨((25975728831/68719476736), (-17344051061/68719476736)), (7/34359738368), by norm_num⟩
  | 3 => ⟨((-72020012809/274877906944), (24043960185/137438953472)), (41/274877906944), by norm_num⟩
  | 4 => ⟨((37440351617/274877906944), (-49998009635/549755813888)), (45/549755813888), by norm_num⟩
  | 5 => ⟨((-31142008995/549755813888), (41587175295/1099511627776)), (5/137438953472), by norm_num⟩
  | 6 => ⟨((5396498933/274877906944), (-28826033303/2199023255552)), (15/1099511627776), by norm_num⟩
  | 7 => ⟨((-12824804641/2199023255552), (34252600647/8796093022208)), (19/4398046511104), by norm_num⟩
  | 8 => ⟨((53336863069/35184372088832), (-8903285087/8796093022208)), (41/35184372088832), by norm_num⟩
  | 9 => ⟨((-24646864171/70368744177664), (32913530431/140737488355328)), (5/17592186044416), by norm_num⟩
  | 10 => ⟨((82002741167/1125899906842624), (-27376704985/562949953421312)), (35/562949953421312), by norm_num⟩
  | 11 => ⟨((-62007238733/4503599627370496), (20701184589/2251799813685248)), (7/562949953421312), by norm_num⟩
  | 12 => ⟨((21490071351/9007199254740992), (-3587241933/2251799813685248)), (41/18014398509481984), by norm_num⟩
  | _ => zero

def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581944238521241/10141204801825835211973625643008), (-766872440141/10141204801825835211973625643008)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((1779562950984651/633825300114114700748351602688), (-113540635693/79228162514264337593543950336)), (181/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((945317593429643/19807040628566084398385987584), (-510862404119/19807040628566084398385987584)), (203/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1890465955485613/2475880078570760549798248448), (-542704932255/1237940039285380274899124224)), (27/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((1772132049483549/154742504910672534362390528), (-271303893919/38685626227668133590597632)), (27/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((775217893565089/4835703278458516698824704), (-508591608619/4835703278458516698824704)), (405/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629780292486729/302231454903657293676544), (-444914491459/302231454903657293676544)), (355/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472261518750679/18889465931478580854784), (-361396334147/18889465931478580854784)), (9/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((1298479704554625/4722366482869645213696), (-1083850698989/4722366482869645213696)), (27/295147905179352825856), by norm_num⟩
  | 9 => ⟨((101421282430215/36893488147419103232), (-1489745178145/590295810358705651712)), (297/295147905179352825856), by norm_num⟩
  | 8 => ⟨((912544730648049/36893488147419103232), (-1861357540839/73786976294838206464)), (371/36893488147419103232), by norm_num⟩
  | 7 => ⟨((912236333799523/4611686018427387904), (-2092894924227/9223372036854775808)), (835/9223372036854775808), by norm_num⟩
  | 6 => ⟨((99732500835579/72057594037927936), (-2091480432803/1152921504606846976)), (835/1152921504606846976), by norm_num⟩
  | 5 => ⟨((598048420864805/72057594037927936), (-28569614153/2251799813685248)), (731/144115188075855872), by norm_num⟩
  | 4 => ⟨((746954456367595/18014398509481984), (-2739505885267/36028797018963968)), (1097/36028797018963968), by norm_num⟩
  | 3 => ⟨((1492092512551695/9007199254740992), (-1709414692131/4503599627370496)), (1371/9007199254740992), by norm_num⟩
  | 2 => ⟨((2233604094182813/4503599627370496), (-6821027442563/4503599627370496)), (343/562949953421312), by norm_num⟩
  | 1 => ⟨((2224553700205969/2251799813685248), (-2547514816549/562949953421312)), (2061/1125899906842624), by norm_num⟩
  | 0 => ⟨((2197497140012765/2251799813685248), (-20214768236919/2251799813685248)), (8269/2251799813685248), by norm_num⟩
  | _ => zero

def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((2197497140012765/2251799813685248), (-20214768236919/2251799813685248)), (31543740279387717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((536080629166481/562949953421312), (-39454568844599/2251799813685248)), (16289/2251799813685248), by norm_num⟩
  | 2 => ⟨((1020641880450983/1125899906842624), (-4696427711105/140737488355328)), (31595/2251799813685248), by norm_num⟩
  | 3 => ⟨((1847940887250129/2251799813685248), (-136235792367197/2251799813685248)), (29/1099511627776), by norm_num⟩
  | 4 => ⟨((1508271432925701/2251799813685248), (-111801985901333/1125899906842624)), (104667/2251799813685248), by norm_num⟩
  | 5 => ⟨((988046968319365/2251799813685248), (-299543041889447/2251799813685248)), (161001/2251799813685248), by norm_num⟩
  | 6 => ⟨((393689870774907/2251799813685248), (-131433794701165/1125899906842624)), (184123/2251799813685248), by norm_num⟩
  | _ => zero

def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-13396700123/8589934592), (-29514604959/4294967296)), (1/4294967296), by norm_num⟩, -1, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨7,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 12 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨7,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 12 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨7,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 12 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨7,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 12 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨7,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 12 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨7,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 12 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨7,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiRectangle.Tile007Terms0
