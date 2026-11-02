/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 34 bits, checked against fixed final error disks.
module

public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile019Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨19,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (5499/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (5499/640))
  have he : value ((3/4), (5499/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-26551852495/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-2489236171/1073741824), (-28517311889/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-26551852495/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((127875674830223/9007199254740992), (-1754845183609207/18014398509481984)), (2135121/4503599627370496), by norm_num⟩
  | 1 => ⟨((-753916053/17179869184), (10346033023/34359738368)), (103/68719476736), by norm_num⟩
  | 2 => ⟨((1165193263/17179869184), (-15990013649/34359738368)), (81/34359738368), by norm_num⟩
  | 3 => ⟨((-2401107895/34359738368), (16475270339/34359738368)), (85/34359738368), by norm_num⟩
  | 4 => ⟨((3710963219/68719476736), (-3182860003/8589934592)), (133/68719476736), by norm_num⟩
  | 5 => ⟨((-2294148971/68719476736), (3935342157/17179869184)), (21/17179869184), by norm_num⟩
  | 6 => ⟨((2363770621/137438953472), (-16219079567/137438953472)), (11/17179869184), by norm_num⟩
  | 7 => ⟨((-4175151623/549755813888), (28647921997/549755813888)), (79/274877906944), by norm_num⟩
  | 8 => ⟨((3226392729/1099511627776), (-22137985773/1099511627776)), (31/274877906944), by norm_num⟩
  | 9 => ⟨((-2216203755/2199023255552), (15206545301/2199023255552)), (87/2199023255552), by norm_num⟩
  | 10 => ⟨((2740151957/8796093022208), (-18801630837/8796093022208)), (55/4398046511104), by norm_num⟩
  | 11 => ⟨((-3079973101/35184372088832), (1320832707/2199023255552)), (125/35184372088832), by norm_num⟩
  | 12 => ⟨((3173442537/140737488355328), (-1360916657/8796093022208)), (131/140737488355328), by norm_num⟩
  | _ => zero

def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395238986542947/2535301200456458802993406410752), (-1857622040979/10141204801825835211973625643008)), (607/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778390950329727/633825300114114700748351602688), (-2197515057565/633825300114114700748351602688)), (2889/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472329197673735/9903520314283042199192993792), (-1235851852835/19807040628566084398385987584)), (1625/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889065278610111/2475880078570760549798248448), (-2625563991239/2475880078570760549798248448)), (1727/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770731506614031/154742504910672534362390528), (-2624865391017/154742504910672534362390528)), (3455/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549122920614723/9671406556917033397649408), (-2460069271601/9671406556917033397649408)), (3239/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258411969246027/604462909807314587353088), (-2151818839199/604462909807314587353088)), (2835/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((117948740105459/4722366482869645213696), (-3495315338723/75557863725914323419136)), (9/147573952589676412928), by norm_num⟩
  | 10 => ⟨((1297080263508149/4722366482869645213696), (-1310135281737/2361183241434822606848)), (3457/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620816667790963/590295810358705651712), (-900224288057/147573952589676412928)), (2377/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822685218288705/73786976294838206464), (-4498160934605/73786976294838206464)), (2973/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1821768679694673/9223372036854775808), (-1264090821141/2305843009213693952)), (6691/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593017008134759/1152921504606846976), (-2525641482869/576460752303423488)), (837/144115188075855872), by norm_num⟩
  | 5 => ⟨((149216602347327/18014398509481984), (-4414163267535/144115188075855872)), (733/18014398509481984), by norm_num⟩
  | 4 => ⟨((745182547185243/18014398509481984), (-6609841310143/36028797018963968)), (8805/36028797018963968), by norm_num⟩
  | 3 => ⟨((371916655995619/2251799813685248), (-4121189603901/4503599627370496)), (5511/4503599627370496), by norm_num⟩
  | 2 => ⟨((2224763995173371/4503599627370496), (-8212563175023/2251799813685248)), (5523/1125899906842624), by norm_num⟩
  | 1 => ⟨((2211322833754573/2251799813685248), (-24489081770867/2251799813685248)), (33261/2251799813685248), by norm_num⟩
  | 0 => ⟨((1085576525305545/1125899906842624), (-24193279997169/1125899906842624)), (33509/1125899906842624), by norm_num⟩
  | _ => zero

def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((1085576525305545/1125899906842624), (-24193279997169/1125899906842624)), (127826694968795421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2092354871581107/2251799813685248), (-93307252893279/2251799813685248)), (132117/2251799813685248), by norm_num⟩
  | 2 => ⟨((1940333522825943/2251799813685248), (-86700373611627/1125899906842624)), (256475/2251799813685248), by norm_num⟩
  | 3 => ⟨((829298043717353/1125899906842624), (-298832321306317/2251799813685248)), (120375/562949953421312), by norm_num⟩
  | 4 => ⟨((1182005704423791/2251799813685248), (-220109316958567/1125899906842624)), (418555/1125899906842624), by norm_num⟩
  | 5 => ⟨((1068785095663673/4503599627370496), (-924311181342753/4503599627370496)), (2412259/4503599627370496), by norm_num⟩
  | 6 => ⟨((127875674830223/9007199254740992), (-1754845183609207/18014398509481984)), (2135121/4503599627370496), by norm_num⟩
  | _ => zero

def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2489236171/1073741824), (-28517311889/1073741824)), (1/536870912), by norm_num⟩, -4, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-6733422557/2147483648), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-2525033459/1073741824), (-28927414563/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-6733422557/2147483648), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-201538635550097/9007199254740992), (-833601122338113/9007199254740992)), (9199737/18014398509481984), by norm_num⟩
  | 1 => ⟨((4821191605/68719476736), (19941341381/68719476736)), (7/4294967296), by norm_num⟩
  | 2 => ⟨((-1889602299/17179869184), (-15631490139/34359738368)), (89/34359738368), by norm_num⟩
  | 3 => ⟨((1974945693/17179869184), (16337482305/34359738368)), (95/34359738368), by norm_num⟩
  | 4 => ⟨((-6192430797/68719476736), (-25613040635/68719476736)), (151/68719476736), by norm_num⟩
  | 5 => ⟨((3883266189/68719476736), (2007738519/8589934592)), (97/68719476736), by norm_num⟩
  | 6 => ⟨((-4058652891/137438953472), (-4196835009/34359738368)), (13/17179869184), by norm_num⟩
  | 7 => ⟨((3635966475/274877906944), (7519515369/137438953472)), (95/274877906944), by norm_num⟩
  | 8 => ⟨((-2850137963/549755813888), (-11788698473/549755813888)), (151/1099511627776), by norm_num⟩
  | 9 => ⟨((1985909133/1099511627776), (2053521993/274877906944)), (107/2199023255552), by norm_num⟩
  | 10 => ⟨((-155670165/274877906944), (-5151045065/2199023255552)), (17/1099511627776), by norm_num⟩
  | 11 => ⟨((5679742859/35184372088832), (11746234187/17592186044416)), (157/35184372088832), by norm_num⟩
  | 12 => ⟨((-5936266961/140737488355328), (-1534593723/8796093022208)), (83/70368744177664), by norm_num⟩
  | _ => zero

def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790456259316641/5070602400912917605986812821504), (-2355138770929/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778338006875255/633825300114114700748351602688), (-1392955058329/316912650057057350374175801344)), (2891/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472314288470289/9903520314283042199192993792), (-3133502728321/39614081257132168796771975168)), (813/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((944500906916229/1237940039285380274899124224), (-3328547505123/2475880078570760549798248448)), (3457/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442666982177813/38685626227668133590597632), (-415956093237/19342813113834066795298816)), (3457/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549063196230841/9671406556917033397649408), (-3118716044117/9671406556917033397649408)), (1621/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314589897604373/151115727451828646838272), (-2727922194421/604462909807314587353088)), (1419/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943547250666417/37778931862957161709568), (-4431084831265/75557863725914323419136)), (1153/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((648508030903393/2361183241434822606848), (-3321749141099/4722366482869645213696)), (3461/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620728071670885/590295810358705651712), (-4564864023217/590295810358705651712)), (4759/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822573995714027/73786976294838206464), (-2851135313045/36893488147419103232)), (93/1152921504606846976), by norm_num⟩
  | 7 => ⟨((1821642899051085/9223372036854775808), (-801227505403/1152921504606846976)), (6701/9223372036854775808), by norm_num⟩
  | 6 => ⟨((49777825320239/36028797018963968), (-6403282303615/1152921504606846976)), (3353/576460752303423488), by norm_num⟩
  | 5 => ⟨((596810564360407/72057594037927936), (-2797762153305/72057594037927936)), (2937/72057594037927936), by norm_num⟩
  | 4 => ⟨((1490195731690549/36028797018963968), (-1047326143671/4503599627370496)), (4411/18014398509481984), by norm_num⟩
  | 3 => ⟨((743725868154467/4503599627370496), (-1305952106371/1125899906842624)), (1381/1125899906842624), by norm_num⟩
  | 2 => ⟨((1112162361281149/2251799813685248), (-20818462604081/4503599627370496)), (11079/2251799813685248), by norm_num⟩
  | 1 => ⟨((1105320187986275/1125899906842624), (-3879541837143/281474976710656)), (2087/140737488355328), by norm_num⟩
  | 0 => ⟨((2169695099928979/2251799813685248), (-61310637591471/2251799813685248)), (16853/562949953421312), by norm_num⟩
  | _ => zero

def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((2169695099928979/2251799813685248), (-61310637591471/2251799813685248)), (64289095165061773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1044457372228791/1125899906842624), (-118150280630879/2251799813685248)), (33395/562949953421312), by norm_num⟩
  | 2 => ⟨((965806395036657/1125899906842624), (-109603820806667/1125899906842624)), (130927/1125899906842624), by norm_num⟩
  | 3 => ⟨((204451787757139/281474976710656), (-188038155811531/1125899906842624)), (977/4398046511104), by norm_num⟩
  | 4 => ⟨((562616787143037/1125899906842624), (-136583143452011/562949953421312)), (893771/2251799813685248), by norm_num⟩
  | 5 => ⟨((859464779787171/4503599627370496), (-1092018484127763/4503599627370496)), (1326937/2251799813685248), by norm_num⟩
  | 6 => ⟨((-201538635550097/9007199254740992), (-833601122338113/9007199254740992)), (9199737/18014398509481984), by norm_num⟩
  | _ => zero

def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2525033459/1073741824), (-28927414563/1073741824)), (1/536870912), by norm_num⟩, -4, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-27299274533/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-2559306987/1073741824), (-29320060675/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-27299274533/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-471018663699967/9007199254740992), (-684224382975857/9007199254740992)), (2352459/4503599627370496), by norm_num⟩
  | 1 => ⟨((2855153405/17179869184), (8295066533/34359738368)), (29/17179869184), by norm_num⟩
  | 2 => ⟨((-9073831215/34359738368), (-823817749/2147483648)), (47/17179869184), by norm_num⟩
  | 3 => ⟨((9612374683/34359738368), (3490849537/8589934592)), (101/34359738368), by norm_num⟩
  | 4 => ⟨((-7637161045/34359738368), (-5547053871/17179869184)), (41/17179869184), by norm_num⟩
  | 5 => ⟨((9708523565/68719476736), (7051534321/34359738368)), (53/34359738368), by norm_num⟩
  | 6 => ⟨((-5142368417/68719476736), (-14940103773/137438953472)), (57/68719476736), by norm_num⟩
  | 7 => ⟨((4669349613/137438953472), (6782922003/137438953472)), (53/137438953472), by norm_num⟩
  | 8 => ⟨((-1854930553/137438953472), (-5389122813/274877906944)), (43/274877906944), by norm_num⟩
  | 9 => ⟨((2620030733/549755813888), (15223931021/2199023255552)), (123/2199023255552), by norm_num⟩
  | 10 => ⟨((-13322557931/8796093022208), (-9676494459/4398046511104)), (79/4398046511104), by norm_num⟩
  | 11 => ⟨((7698146593/17592186044416), (2795674571/4398046511104)), (93/17592186044416), by norm_num⟩
  | 12 => ⟨((-4077520711/35184372088832), (-11846405705/70368744177664)), (25/17592186044416), by norm_num⟩
  | _ => zero

def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197608867455839/1267650600228229401496703205376), (-2831478044127/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778286971907009/633825300114114700748351602688), (-837299662401/158456325028528675187087900672)), (2893/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889199648452713/39614081257132168796771975168), (-3767057900011/39614081257132168796771975168)), (1627/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((236117574081473/309485009821345068724781056), (-4001524836289/2475880078570760549798248448)), (3459/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221325821350421/19342813113834066795298816), (-2000214581605/77371252455336267181195264)), (865/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1549005528035769/9671406556917033397649408), (-1874619248043/4835703278458516698824704)), (3245/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629154492860571/302231454903657293676544), (-3279420186155/604462909807314587353088)), (355/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((943505998527933/37778931862957161709568), (-5326876980139/75557863725914323419136)), (577/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((324238486546717/1180591620717411303424), (-3993250251675/4722366482869645213696)), (433/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1620642277418669/590295810358705651712), (-342976300971/36893488147419103232)), (4765/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822466175895689/73786976294838206464), (-1713720253331/18446744073709551616)), (5959/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910760404926089/4611686018427387904), (-7705358179685/9223372036854775808)), (6709/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592767333380977/1152921504606846976), (-3848692681277/576460752303423488)), (6715/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193512328372635/144115188075855872), (-3363125430103/72057594037927936)), (1471/36028797018963968), by norm_num⟩
  | 4 => ⟨((1490030322567021/36028797018963968), (-5035736918827/18014398509481984)), (8839/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487241126869275/9007199254740992), (-98109831735/70368744177664)), (11073/9007199254740992), by norm_num⟩
  | 2 => ⟨((2223892027472723/4503599627370496), (-25022447154853/4503599627370496)), (5555/1125899906842624), by norm_num⟩
  | 1 => ⟨((552490719918065/562949953421312), (-18650065981503/1125899906842624)), (16759/1125899906842624), by norm_num⟩
  | 0 => ⟨((2168227707636787/2251799813685248), (-18417479845505/562949953421312)), (67791/2251799813685248), by norm_num⟩
  | _ => zero

def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((2168227707636787/2251799813685248), (-18417479845505/562949953421312)), (258602150923918967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2085347066201725/2251799813685248), (-141871545998619/2251799813685248)), (67493/1125899906842624), by norm_num⟩
  | 2 => ⟨((1922260062659877/2251799813685248), (-262768839776693/2251799813685248)), (133513/1125899906842624), by norm_num⟩
  | 3 => ⟨((201285448605513/281474976710656), (-448627842798829/2251799813685248)), (518217/2251799813685248), by norm_num⟩
  | 4 => ⟨((66384295148889/140737488355328), (-320818062230493/1125899906842624)), (473827/1125899906842624), by norm_num⟩
  | 5 => ⟨((318173484112839/2251799813685248), (-605305130312777/2251799813685248)), (358513/562949953421312), by norm_num⟩
  | 6 => ⟨((-471018663699967/9007199254740992), (-684224382975857/9007199254740992)), (2352459/4503599627370496), by norm_num⟩
  | _ => zero

def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2559306987/1073741824), (-29320060675/1073741824)), (1/536870912), by norm_num⟩, -4, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-27649932795/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-162011325/67108864), (-29696675867/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-27649932795/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-657015355250307/9007199254740992), (-932454673985809/18014398509481984)), (2294535/4503599627370496), by norm_num⟩
  | 1 => ⟨((4033757865/17179869184), (11449645263/68719476736)), (57/34359738368), by norm_num⟩
  | 2 => ⟨((-12984165675/34359738368), (-9213746585/34359738368)), (93/34359738368), by norm_num⟩
  | 3 => ⟨((3482868083/8589934592), (9885968713/34359738368)), (51/17179869184), by norm_num⟩
  | 4 => ⟨((-11210919873/34359738368), (-994428303/4294967296)), (21/8589934592), by norm_num⟩
  | 5 => ⟨((14434623581/68719476736), (10243011917/68719476736)), (55/34359738368), by norm_num⟩
  | 6 => ⟨((-3871938407/34359738368), (-10990327811/137438953472)), (15/17179869184), by norm_num⟩
  | 7 => ⟨((14243758781/274877906944), (10107571571/274877906944)), (7/17179869184), by norm_num⟩
  | 8 => ⟨((-11462222699/549755813888), (-2033438611/137438953472)), (23/137438953472), by norm_num⟩
  | 9 => ⟨((16397987353/2199023255552), (363632577/68719476736)), (67/1099511627776), by norm_num⟩
  | 10 => ⟨((-10556617013/4398046511104), (-936390489/549755813888)), (11/549755813888), by norm_num⟩
  | 11 => ⟨((3089130845/4398046511104), (4384181393/8796093022208)), (13/2199023255552), by norm_num⟩
  | 12 => ⟨((-13258038129/70368744177664), (-2352022583/17592186044416)), (113/70368744177664), by norm_num⟩
  | _ => zero

def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((98801941140089/633825300114114700748351602688), (-1644184690249/5070602400912917605986812821504)), (607/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778237703364221/633825300114114700748351602688), (-3889433484013/633825300114114700748351602688)), (1447/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((118071507294673/2475880078570760549798248448), (-4374678443799/39614081257132168796771975168)), (407/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((944440725128357/1237940039285380274899124224), (-580868680651/309485009821345068724781056)), (3461/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770547271156851/154742504910672534362390528), (-2322830000185/77371252455336267181195264)), (1731/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387237441918185/2417851639229258349412352), (-4353936539261/9671406556917033397649408)), (3247/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258260028611175/604462909807314587353088), (-952081281221/151115727451828646838272)), (1421/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((471733032334905/18889465931478580854784), (-6185961576173/75557863725914323419136)), (1155/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1296893772361547/4722366482869645213696), (-4637226048197/4722366482869645213696)), (3467/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620559095326795/590295810358705651712), (-99570920699/9223372036854775808)), (4769/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911180767357761/36893488147419103232), (-7960205858291/73786976294838206464)), (2983/36893488147419103232), by norm_num⟩
  | 7 => ⟨((227675272229931/1152921504606846976), (-8947717496243/9223372036854775808)), (6717/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796323782792553/576460752303423488), (-4469165535099/576460752303423488)), (1681/288230376151711744), by norm_num⟩
  | 5 => ⟨((298351564332207/36028797018963968), (-7810488472165/144115188075855872)), (1473/36028797018963968), by norm_num⟩
  | 4 => ⟨((1489868676377059/36028797018963968), (-1461831446369/4503599627370496)), (8855/36028797018963968), by norm_num⟩
  | 3 => ⟨((743517322299369/4503599627370496), (-3645367597109/2251799813685248)), (11097/9007199254740992), by norm_num⟩
  | 2 => ⟨((277933233548133/562949953421312), (-14526300129497/2251799813685248)), (11141/2251799813685248), by norm_num⟩
  | 1 => ⟨((276161366315963/281474976710656), (-21651860140597/1125899906842624)), (4205/281474976710656), by norm_num⟩
  | 0 => ⟨((541688653943139/562949953421312), (-42755374440773/1125899906842624)), (34079/1125899906842624), by norm_num⟩
  | _ => zero

def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((541688653943139/562949953421312), (-42755374440773/1125899906842624)), (130001072410201671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2081674156072475/2251799813685248), (-164562416882015/2251799813685248)), (136345/2251799813685248), by norm_num⟩
  | 2 => ⟨((1912375370509701/2251799813685248), (-304259133695797/2251799813685248)), (272017/2251799813685248), by norm_num⟩
  | 3 => ⟨((1583003034120089/2251799813685248), (-129198357242113/562949953421312)), (535539/2251799813685248), by norm_num⟩
  | 4 => ⟨((994237207145171/2251799813685248), (-181651486312969/562949953421312)), (499389/1125899906842624), by norm_num⟩
  | 5 => ⟨((409051836311087/4503599627370496), (-10025572951021/35184372088832)), (3053097/4503599627370496), by norm_num⟩
  | 6 => ⟨((-657015355250307/9007199254740992), (-932454673985809/18014398509481984)), (2294535/4503599627370496), by norm_num⟩
  | _ => zero

def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-162011325/67108864), (-29696675867/1073741824)), (1/536870912), by norm_num⟩, -4, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-6996709039/2147483648), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-1311882945/536870912), (-30058517973/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-6996709039/2147483648), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-1503552219428561/18014398509481984), (-216304701611835/9007199254740992)), (8543923/18014398509481984), by norm_num⟩
  | 1 => ⟨((18687127231/68719476736), (5376751705/68719476736)), (27/17179869184), by norm_num⟩
  | 2 => ⟨((-7610558067/17179869184), (-4379494029/34359738368)), (89/34359738368), by norm_num⟩
  | 3 => ⟨((16530621927/34359738368), (4756271445/34359738368)), (49/17179869184), by norm_num⟩
  | 4 => ⟨((-6732295259/17179869184), (-1937048941/17179869184)), (81/34359738368), by norm_num⟩
  | 5 => ⟨((17547574301/68719476736), (5048873959/68719476736)), (107/68719476736), by norm_num⟩
  | 6 => ⟨((-2382153795/17179869184), (-5483239589/137438953472)), (59/68719476736), by norm_num⟩
  | 7 => ⟨((8870042323/137438953472), (2552131989/137438953472)), (7/17179869184), by norm_num⟩
  | 8 => ⟨((-3612431773/137438953472), (-4157546199/549755813888)), (93/549755813888), by norm_num⟩
  | 9 => ⟨((10461912403/1099511627776), (6020305279/2199023255552)), (17/274877906944), by norm_num⟩
  | 10 => ⟨((-13634368233/4398046511104), (-3922947157/4398046511104)), (91/4398046511104), by norm_num⟩
  | 11 => ⟨((16153486523/17592186044416), (580970025/2199023255552)), (55/8796093022208), by norm_num⟩
  | 12 => ⟨((-17543206173/70368744177664), (-5047617139/70368744177664)), (121/70368744177664), by norm_num⟩
  | _ => zero

def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790396370611537/5070602400912917605986812821504), (-3727338723417/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444547518713085/158456325028528675187087900672), (-2204212814251/316912650057057350374175801344)), (181/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((944545209139327/19807040628566084398385987584), (-4958401583269/39614081257132168796771975168)), (3259/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888824239822319/2475880078570760549798248448), (-5266985793549/2475880078570760549798248448)), (3463/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885244942786683/77371252455336267181195264), (-2632752808765/77371252455336267181195264)), (3465/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548895782744969/9671406556917033397649408), (-4934839152571/9671406556917033397649408)), (3249/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258212606027739/604462909807314587353088), (-1079103064375/151115727451828646838272)), (711/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1886854719684229/75557863725914323419136), (-7011223187905/75557863725914323419136)), (4623/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324208852755417/1180591620717411303424), (-5255839773337/4722366482869645213696)), (1735/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((405119588751829/147573952589676412928), (-7222592507147/590295810358705651712)), (2387/295147905179352825856), by norm_num⟩
  | 8 => ⟨((227782483786779/9223372036854775808), (-2255490599071/18446744073709551616)), (1493/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1821286791148611/9223372036854775808), (-10141079239265/9223372036854775808)), (6725/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592530914027769/1152921504606846976), (-5065149926395/576460752303423488)), (6733/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193302768230605/144115188075855872), (-8851894071023/144115188075855872)), (5901/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489710614718031/36028797018963968), (-6626812899545/18014398509481984)), (4435/18014398509481984), by norm_num⟩
  | 3 => ⟨((1486832140875389/9007199254740992), (-16524703421405/9007199254740992)), (695/562949953421312), by norm_num⟩
  | 2 => ⟨((1111523085142151/2251799813685248), (-514415819669/70368744177664)), (5585/1125899906842624), by norm_num⟩
  | 1 => ⟨((552156242105453/562949953421312), (-383340673559/17592186044416)), (8439/562949953421312), by norm_num⟩
  | 0 => ⟨((1082639447507077/1125899906842624), (-24218503128587/562949953421312)), (17127/562949953421312), by norm_num⟩
  | _ => zero

def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((1082639447507077/1125899906842624), (-24218503128587/562949953421312)), (65334322215843023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((519478695492413/562949953421312), (-46575910855363/562949953421312)), (8603/140737488355328), by norm_num⟩
  | 2 => ⟨((475510829997625/562949953421312), (-171917189195731/1125899906842624)), (276815/2251799813685248), by norm_num⟩
  | 3 => ⟨((388527733469939/562949953421312), (-290428962036489/1125899906842624)), (552175/2251799813685248), by norm_num⟩
  | 4 => ⟨((922757366892951/2251799813685248), (-400887168275915/1125899906842624)), (523527/1125899906842624), by norm_num⟩
  | 5 => ⟨((185308720725605/4503599627370496), (-1314225485129777/4503599627370496)), (1603765/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1503552219428561/18014398509481984), (-216304701611835/9007199254740992)), (8543923/18014398509481984), by norm_num⟩
  | _ => zero

def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1311882945/536870912), (-30058517973/1073741824)), (1/536870912), by norm_num⟩, -4, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-28311023105/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-165884901/67108864), (-15203351177/536870912)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-28311023105/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-759703667958615/9007199254740992), (33535658786605/9007199254740992)), (3904733/9007199254740992), by norm_num⟩
  | 1 => ⟨((19102930879/68719476736), (-843262181/68719476736)), (25/17179869184), by norm_num⟩
  | 2 => ⟨((-1967504495/4294967296), (347406823/17179869184)), (167/68719476736), by norm_num⟩
  | 3 => ⟨((8646098465/17179869184), (-381665405/17179869184)), (93/34359738368), by norm_num⟩
  | 4 => ⟨((-7124032517/17179869184), (39309591/2147483648)), (155/68719476736), by norm_num⟩
  | 5 => ⟨((18783719203/68719476736), (-829171195/68719476736)), (13/8589934592), by norm_num⟩
  | 6 => ⟨((-20636024743/137438953472), (14233401/2147483648)), (29/34359738368), by norm_num⟩
  | 7 => ⟨((9716138731/137438953472), (-857800553/274877906944)), (111/274877906944), by norm_num⟩
  | 8 => ⟨((-32022808225/1099511627776), (1413585343/1099511627776)), (185/1099511627776), by norm_num⟩
  | 9 => ⟨((23453767089/2199023255552), (-517660743/1099511627776)), (137/2199023255552), by norm_num⟩
  | 10 => ⟨((-3864989511/1099511627776), (1364900289/8796093022208)), (183/8796093022208), by norm_num⟩
  | 11 => ⟨((9264272667/8796093022208), (-817907035/17592186044416)), (111/17592186044416), by norm_num⟩
  | 12 => ⟨((-20355687595/70368744177664), (28080085/2199023255552)), (31/17592186044416), by norm_num⟩
  | _ => zero

def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790377935240215/5070602400912917605986812821504), (1008702802245/2535301200456458802993406410752)), (607/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((889072339287179/316912650057057350374175801344), (2385929350989/316912650057057350374175801344)), (2897/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889039259883011/39614081257132168796771975168), (5367157180039/39614081257132168796771975168)), (815/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888769765975739/2475880078570760549798248448), (5701163083019/2475880078570760549798248448)), (3465/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885217639529079/77371252455336267181195264), (356221351549/9671406556917033397649408)), (1733/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774422224149011/4835703278458516698824704), (333849861855/604462909807314587353088)), (3251/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258167547684249/604462909807314587353088), (1168043984203/151115727451828646838272)), (1423/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((471695309087255/18889465931478580854784), (7589057658685/75557863725914323419136)), (2313/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296780068223939/4722366482869645213696), (5688969289235/4722366482869645213696)), (217/295147905179352825856), by norm_num⟩
  | 9 => ⟨((1620401884972031/590295810358705651712), (244304539407/18446744073709551616)), (4777/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911081861583663/36893488147419103232), (9765302786821/73786976294838206464)), (747/9223372036854775808), by norm_num⟩
  | 7 => ⟨((910588928873361/4611686018427387904), (1372063916299/1152921504606846976)), (6731/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592421023081959/1152921504606846976), (10964699502287/1152921504606846976)), (1685/288230376151711744), by norm_num⟩
  | 5 => ⟨((149150692448825/18014398509481984), (4790416045787/72057594037927936)), (5907/144115188075855872), by norm_num⟩
  | 4 => ⟨((744781315779533/18014398509481984), (14344709058597/36028797018963968)), (8881/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486643434383263/9007199254740992), (8942244988163/4503599627370496)), (11137/9007199254740992), by norm_num⟩
  | 2 => ⟨((69458051429571/140737488355328), (8907494880763/1125899906842624)), (5595/1125899906842624), by norm_num⟩
  | 1 => ⟨((552003662713919/562949953421312), (6637266293805/281474976710656)), (16919/1125899906842624), by norm_num⟩
  | 0 => ⟨((1081974810225271/1125899906842624), (26203223420265/562949953421312)), (34377/1125899906842624), by norm_num⟩
  | _ => zero

def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((1081974810225271/1125899906842624), (26203223420265/562949953421312)), (131137852195357921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1037324052692023/1125899906842624), (50361897207963/562949953421312)), (69273/1125899906842624), by norm_num⟩
  | 2 => ⟨((946705742716479/1125899906842624), (92799736451751/562949953421312)), (70021/562949953421312), by norm_num⟩
  | 3 => ⟨((191359061696495/281474976710656), (312120261801313/1125899906842624)), (140839/562949953421312), by norm_num⟩
  | 4 => ⟨((433851701290855/1125899906842624), (848772294187421/2251799813685248)), (1078335/2251799813685248), by norm_num⟩
  | 5 => ⟨((28861168985105/4503599627370496), (1308255917257933/4503599627370496)), (3287923/4503599627370496), by norm_num⟩
  | 6 => ⟨((-759703667958615/9007199254740992), (33535658786605/9007199254740992)), (3904733/9007199254740992), by norm_num⟩
  | _ => zero

def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-165884901/67108864), (-15203351177/536870912)), (1/536870912), by norm_num⟩, -5, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨19,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 12 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨19,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 12 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨19,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 12 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨19,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 12 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨19,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 12 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨19,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiRectangle.Tile019Terms3
