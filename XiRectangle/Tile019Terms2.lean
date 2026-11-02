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
namespace Reinmann.XiRectangle.Tile019Terms2
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
  | 0 => ⟨((-23816355775/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-1116391677/536870912), (-12789662149/536870912)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-23816355775/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((290162044307179/9007199254740992), (543933954619541/4503599627370496)), (2587629/4503599627370496), by norm_num⟩
  | 1 => ⟨((-3068923995/34359738368), (-23011858341/68719476736)), (7/4294967296), by norm_num⟩
  | 2 => ⟨((4254432029/34359738368), (15950604729/34359738368)), (79/34359738368), by norm_num⟩
  | 3 => ⟨((-491491261/4294967296), (-460671529/1073741824)), (75/34359738368), by norm_num⟩
  | 4 => ⟨((5450812509/68719476736), (638626343/2147483648)), (53/34359738368), by norm_num⟩
  | 5 => ⟨((-1511286129/34359738368), (-22664296913/137438953472)), (15/17179869184), by norm_num⟩
  | 6 => ⟨((5586899837/274877906944), (20946258007/274877906944)), (113/274877906944), by norm_num⟩
  | 7 => ⟨((-4425764423/549755813888), (-4148239909/137438953472)), (91/549755813888), by norm_num⟩
  | 8 => ⟨((6135412263/2199023255552), (11501363189/1099511627776)), (1/17179869184), by norm_num⟩
  | 9 => ⟨((-3780216633/4398046511104), (-14172688831/4398046511104)), (81/4398046511104), by norm_num⟩
  | 10 => ⟨((2096197201/8796093022208), (15718014887/17592186044416)), (91/17592186044416), by norm_num⟩
  | 11 => ⟨((-4226831069/70368744177664), (-3961780983/17592186044416)), (47/35184372088832), by norm_num⟩
  | 12 => ⟨((488302673/35184372088832), (14645852365/281474976710656)), (89/281474976710656), by norm_num⟩
  | _ => zero

def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581267062326325/10141204801825835211973625643008), (213325301501/1267650600228229401496703205376)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778759468164861/633825300114114700748351602688), (1009829576709/316912650057057350374175801344)), (2889/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944865657505687/19807040628566084398385987584), (2271701666161/39614081257132168796771975168)), (1625/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889505641496681/2475880078570760549798248448), (603292712481/618970019642690137449562112)), (3453/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885585895820125/77371252455336267181195264), (2412594833727/154742504910672534362390528)), (1727/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((193691950637609/1208925819614629174706176), (141324738033/604462909807314587353088)), (3239/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629386492723105/302231454903657293676544), (1977934674611/604462909807314587353088)), (2835/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943883168952247/37778931862957161709568), (1606498695957/37778931862957161709568)), (4607/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297519999953027/4722366482869645213696), (2408745300405/4722366482869645213696)), (27/36893488147419103232), by norm_num⟩
  | 9 => ⟨((1621421084864125/590295810358705651712), (3310396087045/590295810358705651712)), (4753/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911720204414047/36893488147419103232), (4135553381865/73786976294838206464)), (5943/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455654453552089/2305843009213693952), (1162285582855/2305843009213693952)), (6689/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593865574109715/1152921504606846976), (2322475763811/576460752303423488)), (6693/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194474674422529/144115188075855872), (4059622363971/144115188075855872)), (5861/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491476598725775/36028797018963968), (6080024170369/36028797018963968)), (8799/36028797018963968), by norm_num⟩
  | 3 => ⟨((372263441530341/2251799813685248), (3791794343841/4503599627370496)), (5507/4503599627370496), by norm_num⟩
  | 2 => ⟨((2227531565130093/4503599627370496), (1889744025275/562949953421312)), (22071/4503599627370496), by norm_num⟩
  | 1 => ⟨((2215457405153981/2251799813685248), (5638553179067/562949953421312)), (8305/562949953421312), by norm_num⟩
  | 0 => ⟨((272419384293519/281474976710656), (22309821327913/1125899906842624)), (66895/2251799813685248), by norm_num⟩
  | _ => zero

def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((272419384293519/281474976710656), (22309821327913/1125899906842624)), (255184182173918967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2108356879116393/2251799813685248), (86368285534611/2251799813685248)), (66069/1125899906842624), by norm_num⟩
  | 2 => ⟨((492684698479987/562949953421312), (40433249847013/562949953421312)), (128789/1125899906842624), by norm_num⟩
  | 3 => ⟨((1713142441581715/2251799813685248), (283092212916949/2251799813685248)), (243929/1125899906842624), by norm_num⟩
  | 4 => ⟨((1267748494686291/2251799813685248), (107686589607539/562949953421312)), (216245/562949953421312), by norm_num⟩
  | 5 => ⟨((1262673361849057/4503599627370496), (242507368626935/1125899906842624)), (2609761/4503599627370496), by norm_num⟩
  | 6 => ⟨((290162044307179/9007199254740992), (543933954619541/4503599627370496)), (2587629/4503599627370496), by norm_num⟩
  | _ => zero

def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1116391677/536870912), (-12789662149/536870912)), (1/536870912), by norm_num⟩, -4, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-24337117311/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-570401187/268435456), (-26138634393/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-24337117311/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((757814221193973/9007199254740992), (190915238177399/2251799813685248)), (3835821/9007199254740992), by norm_num⟩
  | 1 => ⟨((-16380686675/68719476736), (-16507067883/68719476736)), (85/68719476736), by norm_num⟩
  | 2 => ⟨((5801247509/17179869184), (5846005625/17179869184)), (31/17179869184), by norm_num⟩
  | 3 => ⟨((-10957447903/34359738368), (-11041987431/34359738368)), (15/8589934592), by norm_num⟩
  | 4 => ⟨((970149613/4294967296), (15642153067/68719476736)), (87/68719476736), by norm_num⟩
  | 5 => ⟨((-4397825327/34359738368), (-138492365/1073741824)), (51/68719476736), by norm_num⟩
  | 6 => ⟨((8306651601/137438953472), (16741479107/274877906944)), (49/137438953472), by norm_num⟩
  | 7 => ⟨((-13448294949/549755813888), (-6776026001/274877906944)), (81/549755813888), by norm_num⟩
  | 8 => ⟨((595342011/68719476736), (9598963643/1099511627776)), (59/1099511627776), by norm_num⟩
  | 9 => ⟨((-11994531057/4398046511104), (-3021767987/1099511627776)), (19/1099511627776), by norm_num⟩
  | 10 => ⟨((13593226179/17592186044416), (6849050707/8796093022208)), (11/2199023255552), by norm_num⟩
  | 11 => ⟨((-7002274509/35184372088832), (-14112597715/70368744177664)), (93/70368744177664), by norm_num⟩
  | 12 => ⟨((13225958385/281474976710656), (13328000055/281474976710656)), (45/140737488355328), by norm_num⟩
  | _ => zero

def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581207834572315/10141204801825835211973625643008), (257018613787/2535301200456458802993406410752)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444672692371649/158456325028528675187087900672), (152071460701/79228162514264337593543950336)), (1443/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944827061011371/19807040628566084398385987584), (1368389145853/39614081257132168796771975168)), (3247/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236177968016649/309485009821345068724781056), (363399587051/618970019642690137449562112)), (1725/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((221386253673159/19342813113834066795298816), (1453243967783/154742504910672534362390528)), (3451/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774729548227931/4835703278458516698824704), (681019903673/4835703278458516698824704)), (3235/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258706183756593/604462909807314587353088), (1191408550337/604462909807314587353088)), (2831/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471914513446589/18889465931478580854784), (1935333646285/75557863725914323419136)), (4601/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297439021713401/4722366482869645213696), (725441710805/2361183241434822606848)), (3451/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405327530259839/147573952589676412928), (1993962906113/590295810358705651712)), (2373/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1823302275273717/73786976294838206464), (1245475924463/36893488147419103232)), (2967/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1822463198332061/9223372036854775808), (1400128681005/4611686018427387904)), (6677/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593711937104391/1152921504606846976), (699420063031/288230376151711744)), (6679/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194341341083113/144115188075855872), (2445074028791/144115188075855872)), (5847/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491278791331665/36028797018963968), (3661826293237/36028797018963968)), (8775/36028797018963968), by norm_num⟩
  | 3 => ⟨((744405165840553/4503599627370496), (2283588353519/4503599627370496)), (5489/4503599627370496), by norm_num⟩
  | 2 => ⟨((278382015209755/562949953421312), (1138012929111/562949953421312)), (10991/2251799813685248), by norm_num⟩
  | 1 => ⟨((553693158161693/562949953421312), (13580769423593/2251799813685248)), (16521/1125899906842624), by norm_num⟩
  | 0 => ⟨((136131129925385/140737488355328), (26861427208035/2251799813685248)), (66359/2251799813685248), by norm_num⟩
  | _ => zero

def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((136131129925385/140737488355328), (26861427208035/2251799813685248)), (253139504439543967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1053244092969459/1125899906842624), (3247781099381/140737488355328)), (129959/2251799813685248), by norm_num⟩
  | 2 => ⟨((492338633028049/562949953421312), (48611159658391/1125899906842624)), (31143/281474976710656), by norm_num⟩
  | 3 => ⟨((859069503040269/1125899906842624), (170055272236315/2251799813685248)), (228651/1125899906842624), by norm_num⟩
  | 4 => ⟨((1298109552561067/2251799813685248), (129753362018751/1125899906842624)), (766921/2251799813685248), by norm_num⟩
  | 5 => ⟨((1436845905038113/4503599627370496), (149599513855363/1125899906842624)), (2121981/4503599627370496), by norm_num⟩
  | 6 => ⟨((757814221193973/9007199254740992), (190915238177399/2251799813685248)), (3835821/9007199254740992), by norm_num⟩
  | _ => zero

def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-570401187/268435456), (-26138634393/1073741824)), (1/536870912), by norm_num⟩, -4, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-24828104347/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-2327634783/1073741824), (-26665965977/1073741824)), (3/1073741824), by norm_num⟩
  | 1 => ⟨((-24828104347/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((985241723865115/9007199254740992), (302748205089931/9007199254740992)), (3905967/9007199254740992), by norm_num⟩
  | 1 => ⟨((-21726340129/68719476736), (-6676138777/68719476736)), (11/8589934592), by norm_num⟩
  | 2 => ⟨((7849649989/17179869184), (4824130743/34359738368)), (65/34359738368), by norm_num⟩
  | 3 => ⟨((-15125604425/34359738368), (-580980469/4294967296)), (1/536870912), by norm_num⟩
  | 4 => ⟨((10929654963/34359738368), (3358499079/34359738368)), (95/68719476736), by norm_num⟩
  | 5 => ⟨((-25272612823/137438953472), (-3882924355/68719476736)), (7/8589934592), by norm_num⟩
  | 6 => ⟨((24349082117/274877906944), (7482063263/274877906944)), (111/274877906944), by norm_num⟩
  | 7 => ⟨((-20107971223/549755813888), (-3089420621/274877906944)), (47/274877906944), by norm_num⟩
  | 8 => ⟨((14529878033/1099511627776), (279049191/68719476736)), (35/549755813888), by norm_num⟩
  | 9 => ⟨((-4666305457/1099511627776), (-5735508627/4398046511104)), (23/1099511627776), by norm_num⟩
  | 10 => ⟨((21579772011/17592186044416), (6631100861/17592186044416)), (27/4398046511104), by norm_num⟩
  | 11 => ⟨((-22681295841/70368744177664), (-6969580601/70368744177664)), (115/70368744177664), by norm_num⟩
  | 12 => ⟨((21852458977/281474976710656), (3357446489/140737488355328)), (113/281474976710656), by norm_num⟩
  | _ => zero

def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395287998290011/2535301200456458802993406410752), (388341281229/10141204801825835211973625643008)), (3641/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778625371221599/633825300114114700748351602688), (14359720519/19807040628566084398385987584)), (4325/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((3690587111547/77371252455336267181195264), (516852363473/39614081257132168796771975168)), (4865/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889345695358075/2475880078570760549798248448), (17157319959/77371252455336267181195264)), (2585/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771012056145117/154742504910672534362390528), (548897720623/154742504910672534362390528)), (2585/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774693038376839/4835703278458516698824704), (128611652601/2417851639229258349412352)), (4847/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258642371676499/604462909807314587353088), (112498958793/151115727451828646838272)), (4241/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887554509346303/75557863725914323419136), (365485783537/37778931862957161709568)), (1723/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((324340373672789/1180591620717411303424), (547991082471/4722366482869645213696)), (2585/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((405300933638893/147573952589676412928), (376550931939/295147905179352825856)), (7109/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823169611571117/73786976294838206464), (58799930753/4611686018427387904)), (4443/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1822314390267345/9223372036854775808), (1057604008847/9223372036854775808)), (4999/4611686018427387904), by norm_num⟩
  | 6 => ⟨((199195459553219/144115188075855872), (1056611488087/1152921504606846976)), (9999/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149276528451399/18014398509481984), (923419716373/144115188075855872)), (8751/144115188075855872), by norm_num⟩
  | 4 => ⟨((745543173701955/18014398509481984), (1382902024741/36028797018963968)), (13129/36028797018963968), by norm_num⟩
  | 3 => ⟨((1488571916107095/9007199254740992), (215592041487/1125899906842624)), (513/281474976710656), by norm_num⟩
  | 2 => ⟨((2226585681987123/4503599627370496), (859456766819/1125899906842624)), (32847/4503599627370496), by norm_num⟩
  | 1 => ⟨((2214082859134593/2251799813685248), (160241386811/70368744177664)), (24655/1125899906842624), by norm_num⟩
  | 0 => ⟨((272097690326279/281474976710656), (10139968608801/2251799813685248)), (49391/1125899906842624), by norm_num⟩
  | _ => zero

def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((272097690326279/281474976710656), (10139968608801/2251799813685248)), (188411716941451671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((526054197781837/562949953421312), (4901078722305/562949953421312)), (191873/2251799813685248), by norm_num⟩
  | 2 => ⟨((1966135687547775/2251799813685248), (9159723772455/562949953421312)), (361937/2251799813685248), by norm_num⟩
  | 3 => ⟨((429028716244013/562949953421312), (31990871813121/1125899906842624)), (321911/1125899906842624), by norm_num⟩
  | 4 => ⟨((326511769430029/562949953421312), (48761004711331/1125899906842624)), (1017911/2251799813685248), by norm_num⟩
  | 5 => ⟨((1506571247222351/4503599627370496), (14140725859131/281474976710656)), (2537897/4503599627370496), by norm_num⟩
  | 6 => ⟨((985241723865115/9007199254740992), (302748205089931/9007199254740992)), (3905967/9007199254740992), by norm_num⟩
  | _ => zero

def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2327634783/1073741824), (-26665965977/1073741824)), (3/1073741824), by norm_num⟩, -4, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-25292538241/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-592793865/268435456), (-27164778865/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-25292538241/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((488035944409625/4503599627370496), (-163964891723393/9007199254740992)), (2234563/9007199254740992), by norm_num⟩
  | 1 => ⟨((-21926758697/68719476736), (3683354327/68719476736)), (13/17179869184), by norm_num⟩
  | 2 => ⟨((4035125187/8589934592), (-1355676507/17179869184)), (5/4294967296), by norm_num⟩
  | 3 => ⟨((-7920786591/17179869184), (1330568917/17179869184)), (41/34359738368), by norm_num⟩
  | 4 => ⟨((1457642049/4294967296), (-489722373/8589934592)), (31/34359738368), by norm_num⟩
  | 5 => ⟨((-27468403627/137438953472), (4614264461/137438953472)), (75/137438953472), by norm_num⟩
  | 6 => ⟨((26959679445/274877906944), (-4528806713/274877906944)), (19/68719476736), by norm_num⟩
  | 7 => ⟨((-22680323149/549755813888), (3809941433/549755813888)), (33/274877906944), by norm_num⟩
  | 8 => ⟨((16695206885/1099511627776), (-350566877/137438953472)), (25/549755813888), by norm_num⟩
  | 9 => ⟨((-21848007963/4398046511104), (3670125431/4398046511104)), (67/4398046511104), by norm_num⟩
  | 10 => ⟨((25732050505/17592186044416), (-4322584151/17592186044416)), (81/17592186044416), by norm_num⟩
  | 11 => ⟨((-860982415/2199023255552), (578526603/8796093022208)), (89/70368744177664), by norm_num⟩
  | 12 => ⟨((13520587643/140737488355328), (-1135624187/70368744177664)), (45/140737488355328), by norm_num⟩
  | _ => zero

def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790549585858251/5070602400912917605986812821504), (-216794389977/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778562949317385/633825300114114700748351602688), (-256508272885/633825300114114700748351602688)), (2883/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889510394228711/39614081257132168796771975168), (-288516384495/39614081257132168796771975168)), (3243/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472317780731691/618970019642690137449562112), (-306479627891/2475880078570760549798248448)), (1723/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770937508880491/154742504910672534362390528), (-19150125009/9671406556917033397649408)), (1723/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549316215421543/9671406556917033397649408), (-287169423441/9671406556917033397649408)), (3231/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314645317431695/151115727451828646838272), (-1962428321/4722366482869645213696)), (2827/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887455268743659/75557863725914323419136), (-204015309447/37778931862957161709568)), (4593/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324321777004993/1180591620717411303424), (-76471966917/1180591620717411303424)), (1723/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((202637690497071/73786976294838206464), (-210188205315/295147905179352825856)), (2369/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1823041954900873/73786976294838206464), (-262570809865/36893488147419103232)), (2961/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1822170922882661/9223372036854775808), (-295166223415/4611686018427387904)), (6663/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593420391790361/1152921504606846976), (-147442033017/288230376151711744)), (6663/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194087058856511/144115188075855872), (-515412988683/144115188075855872)), (5831/144115188075855872), by norm_num⟩
  | 4 => ⟨((745449502073183/18014398509481984), (-385926522539/18014398509481984)), (8747/36028797018963968), by norm_num⟩
  | 3 => ⟨((744169226340121/4503599627370496), (-962604119279/9007199254740992)), (10935/9007199254740992), by norm_num⟩
  | 2 => ⟨((2226120895542353/4503599627370496), (-1918587963597/4503599627370496)), (5469/1125899906842624), by norm_num⟩
  | 1 => ⟨((276673875964245/281474976710656), (-89418378755/70368744177664)), (32829/2251799813685248), by norm_num⟩
  | 0 => ⟨((271927374578537/281474976710656), (-5657140997475/2251799813685248)), (65721/2251799813685248), by norm_num⟩
  | _ => zero

def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((271927374578537/281474976710656), (-5657140997475/2251799813685248)), (250705727584075217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2101614796699901/2251799813685248), (-10930502718509/2251799813685248)), (127315/2251799813685248), by norm_num⟩
  | 2 => ⟨((980696696699265/1125899906842624), (-10201486876843/1125899906842624)), (238885/2251799813685248), by norm_num⟩
  | 3 => ⟨((854127382672189/1125899906842624), (-8885838271003/562949953421312)), (105121/562949953421312), by norm_num⟩
  | 4 => ⟨((647675471781755/1125899906842624), (-26963809976835/1125899906842624)), (40703/140737488355328), by norm_num⟩
  | 5 => ⟨((371930459496685/1125899906842624), (-124087750547945/4503599627370496)), (97557/281474976710656), by norm_num⟩
  | 6 => ⟨((488035944409625/4503599627370496), (-163964891723393/9007199254740992)), (2234563/9007199254740992), by norm_num⟩
  | _ => zero

def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-592793865/268435456), (-27164778865/1073741824)), (1/536870912), by norm_num⟩, -4, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-25733144285/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-2412482277/1073741824), (-27638000083/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-25733144285/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((391089786822977/4503599627370496), (-135842750661537/2251799813685248)), (1516385/4503599627370496), by norm_num⟩
  | 1 => ⟨((-8938600893/34359738368), (12419083017/68719476736)), (9/8589934592), by norm_num⟩
  | 2 => ⟨((3347206897/8589934592), (-9301061951/34359738368)), (7/4294967296), by norm_num⟩
  | 3 => ⟨((-6684890485/17179869184), (1160978811/4294967296)), (29/17179869184), by norm_num⟩
  | 4 => ⟨((20026142171/68719476736), (-3477981693/17179869184)), (89/68719476736), by norm_num⟩
  | 5 => ⟨((-11998592083/68719476736), (2083820401/17179869184)), (55/68719476736), by norm_num⟩
  | 6 => ⟨((2995380795/34359738368), (-8323424037/137438953472)), (57/137438953472), by norm_num⟩
  | 7 => ⟨((-1281908417/34359738368), (3562107145/137438953472)), (25/137438953472), by norm_num⟩
  | 8 => ⟨((7680508833/549755813888), (-1333889917/137438953472)), (77/1099511627776), by norm_num⟩
  | 9 => ⟨((-5113055153/1099511627776), (3551979621/1099511627776)), (53/2199023255552), by norm_num⟩
  | 10 => ⟨((12253875471/8796093022208), (-8512623989/8796093022208)), (33/4398046511104), by norm_num⟩
  | 11 => ⟨((-6674423677/17592186044416), (9273288151/35184372088832)), (37/17592186044416), by norm_num⟩
  | 12 => ⟨((13329857611/140737488355328), (-9260096199/140737488355328)), (19/35184372088832), by norm_num⟩
  | _ => zero

def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581049060283875/10141204801825835211973625643008), (-790883484851/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((111156451644677/39614081257132168796771975168), (-935703520321/633825300114114700748351602688)), (2885/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889443194518389/39614081257132168796771975168), (-1052460691231/39614081257132168796771975168)), (1623/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889199707485401/2475880078570760549798248448), (-139747907699/309485009821345068724781056)), (3449/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885433037873921/77371252455336267181195264), (-558847563541/77371252455336267181195264)), (3449/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549249228082341/9671406556917033397649408), (-261883285331/2417851639229258349412352)), (1617/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258522637049761/604462909807314587353088), (-114535696725/75557863725914323419136)), (1415/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((471839988881113/18889465931478580854784), (-1488390693553/75557863725914323419136)), (2299/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297215592423339/4722366482869645213696), (-1115791571895/4722366482869645213696)), (3449/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621003140260509/590295810358705651712), (-1533399017261/590295810358705651712)), (593/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1822918900753475/73786976294838206464), (-1915527983771/73786976294838206464)), (2965/36893488147419103232), by norm_num⟩
  | 7 => ⟨((911016192387803/4611686018427387904), (-538322925745/2305843009213693952)), (417/576460752303423488), by norm_num⟩
  | 6 => ⟨((99580107894869/72057594037927936), (-2151197059559/1152921504606846976)), (6675/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193965583794885/144115188075855872), (-939971819361/72057594037927936)), (2921/72057594037927936), by norm_num⟩
  | 4 => ⟨((11646222713179/281474976710656), (-351901823351/4503599627370496)), (8767/36028797018963968), by norm_num⟩
  | 3 => ⟨((744054918504991/4503599627370496), (-3510806773837/9007199254740992)), (10965/9007199254740992), by norm_num⟩
  | 2 => ⟨((2225662191862413/4503599627370496), (-6997039317383/4503599627370496)), (21951/4503599627370496), by norm_num⟩
  | 1 => ⟨((553174827812313/562949953421312), (-5217166709995/1125899906842624)), (8245/562949953421312), by norm_num⟩
  | 0 => ⟨((2174021278021113/2251799813685248), (-20625020735325/2251799813685248)), (33087/1125899906842624), by norm_num⟩
  | _ => zero

def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((2174021278021113/2251799813685248), (-20625020735325/2251799813685248)), (126216892722701671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((524685087134127/562949953421312), (-39825239939815/2251799813685248)), (64495/1125899906842624), by norm_num⟩
  | 2 => ⟨((977690151246797/1125899906842624), (-74236472926115/2251799813685248)), (15313/140737488355328), by norm_num⟩
  | 3 => ⟨((847766539961421/1125899906842624), (-128928456254517/2251799813685248)), (110417/562949953421312), by norm_num⟩
  | 4 => ⟨((79331260401951/140737488355328), (-97078994853081/1125899906842624)), (715701/2251799813685248), by norm_num⟩
  | 5 => ⟨((43671332870409/140737488355328), (-437773850322255/4503599627370496)), (930277/2251799813685248), by norm_num⟩
  | 6 => ⟨((391089786822977/4503599627370496), (-135842750661537/2251799813685248)), (1516385/4503599627370496), by norm_num⟩
  | _ => zero

def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2412482277/1073741824), (-27638000083/1073741824)), (1/536870912), by norm_num⟩, -4, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-6538062151/2147483648), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-2451773307/1073741824), (-3511015993/134217728)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-6538062151/2147483648), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((475550672622595/9007199254740992), (-196356857706439/2251799813685248)), (3733703/9007199254740992), by norm_num⟩
  | 1 => ⟨((-2761506449/17179869184), (18243800631/68719476736)), (89/68719476736), by norm_num⟩
  | 2 => ⟨((4203734173/17179869184), (-13885915093/34359738368)), (35/17179869184), by norm_num⟩
  | 3 => ⟨((-1066530251/4294967296), (3522998339/8589934592)), (73/34359738368), by norm_num⟩
  | 4 => ⟨((6494150559/34359738368), (-10725847491/34359738368)), (57/34359738368), by norm_num⟩
  | 5 => ⟨((-1977158709/17179869184), (3265508335/17179869184)), (71/68719476736), by norm_num⟩
  | 6 => ⟨((8026005403/137438953472), (-13255884529/137438953472)), (37/68719476736), by norm_num⟩
  | 7 => ⟨((-6981529581/274877906944), (11530810823/274877906944)), (33/137438953472), by norm_num⟩
  | 8 => ⟨((5313855865/549755813888), (-8776453069/549755813888)), (103/1099511627776), by norm_num⟩
  | 9 => ⟨((-7190290405/2199023255552), (11875603685/2199023255552)), (9/274877906944), by norm_num⟩
  | 10 => ⟨((8756400189/8796093022208), (-903888547/549755813888)), (45/4398046511104), by norm_num⟩
  | 11 => ⟨((-9694202491/35184372088832), (16011106691/35184372088832)), (51/17592186044416), by norm_num⟩
  | 12 => ⟨((9838072333/140737488355328), (-16248724525/140737488355328)), (53/70368744177664), by norm_num⟩
  | _ => zero

def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581001394306545/10141204801825835211973625643008), (-1336956835897/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778445962727517/633825300114114700748351602688), (-790836874913/316912650057057350374175801344)), (2887/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944689368447853/19807040628566084398385987584), (-889514456515/19807040628566084398385987584)), (203/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((1889131172883231/2475880078570760549798248448), (-1889777969051/2475880078570760549798248448)), (3451/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770797486782617/154742504910672534362390528), (-118080179775/9671406556917033397649408)), (863/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1549184868214125/9671406556917033397649408), (-885338416027/4835703278458516698824704)), (809/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258466264505155/604462909807314587353088), (-1548816556295/604462909807314587353088)), (2833/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471817060535131/18889465931478580854784), (-1257920839511/37778931862957161709568)), (1151/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((162143339124953/590295810358705651712), (-943009798411/2361183241434822606848)), (3453/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620908277888289/590295810358705651712), (-2591877511381/590295810358705651712)), (4749/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911400046706181/36893488147419103232), (-3237749079709/73786976294838206464)), (2969/36893488147419103232), by norm_num⟩
  | 7 => ⟨((910949205863683/4611686018427387904), (-909896351411/2305843009213693952)), (3341/4611686018427387904), by norm_num⟩
  | 6 => ⟨((796573680342497/576460752303423488), (-1817992892693/576460752303423488)), (6685/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149230946680853/18014398509481984), (-3177442476059/144115188075855872)), (5853/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490538614016457/36028797018963968), (-74345074155/562949953421312)), (4393/18014398509481984), by norm_num⟩
  | 3 => ⟨((371971485324629/2251799813685248), (-741686614153/1125899906842624)), (5497/4503599627370496), by norm_num⟩
  | 2 => ⟨((1112604920365639/2251799813685248), (-11824747298607/4503599627370496)), (22023/4503599627370496), by norm_num⟩
  | 1 => ⟨((69125296303953/70368744177664), (-2203984464357/281474976710656)), (8281/562949953421312), by norm_num⟩
  | 0 => ⟨((2172596983367359/2251799813685248), (-34844870889403/2251799813685248)), (66605/2251799813685248), by norm_num⟩
  | _ => zero

def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((2172596983367359/2251799813685248), (-34844870889403/2251799813685248)), (254077919966887717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((523910191575455/562949953421312), (-16809633991453/562949953421312)), (130587/2251799813685248), by norm_num⟩
  | 2 => ⟨((243537923198381/281474976710656), (-62575641129395/1125899906842624)), (125431/1125899906842624), by norm_num⟩
  | 3 => ⟨((1678756351192827/2251799813685248), (-54141728197479/562949953421312)), (115497/562949953421312), by norm_num⟩
  | 4 => ⟨((615357022882823/1125899906842624), (-161454441062989/1125899906842624)), (97213/281474976710656), by norm_num⟩
  | 5 => ⟨((1252675222475293/4503599627370496), (-705939301210855/4503599627370496)), (536575/1125899906842624), by norm_num⟩
  | 6 => ⟨((475550672622595/9007199254740992), (-196356857706439/2251799813685248)), (3733703/9007199254740992), by norm_num⟩
  | _ => zero

def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2451773307/1073741824), (-3511015993/134217728)), (1/536870912), by norm_num⟩, -4, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨19,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 12 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨19,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 12 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨19,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 12 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨19,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 12 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨19,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 12 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨19,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiRectangle.Tile019Terms2
