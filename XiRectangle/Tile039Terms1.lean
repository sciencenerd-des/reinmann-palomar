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
namespace Reinmann.XiRectangle.Tile039Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨39,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((17/32), (7191/512)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((17/32), (7191/512))
  have he : value ((17/32), (7191/512))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-1179625963/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-9791817/8388608), (-64717791/2097152)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1179625963/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((595203695659981/2251799813685248), (739839000426203/4503599627370496)), (135591687/4503599627370496), by norm_num⟩
  | 1 => ⟨((-311802909/536870912), (-775142877/2147483648)), (145/2147483648), by norm_num⟩
  | 2 => ⟨((685101015/1073741824), (425790745/1073741824)), (81/1073741824), by norm_num⟩
  | 3 => ⟨((-125443399/268435456), (-155926315/536870912)), (121/2147483648), by norm_num⟩
  | 4 => ⟨((551254639/2147483648), (685210263/4294967296)), (17/536870912), by norm_num⟩
  | 5 => ⟨((-968984193/8589934592), (-150556083/2147483648)), (61/4294967296), by norm_num⟩
  | 6 => ⟨((709691961/17179869184), (441074035/17179869184)), (23/4294967296), by norm_num⟩
  | 7 => ⟨((-55691165/4294967296), (-553793549/68719476736)), (59/34359738368), by norm_num⟩
  | 8 => ⟨((244731993/68719476736), (304202199/137438953472)), (33/68719476736), by norm_num⟩
  | 9 => ⟨((-955966489/1099511627776), (-594133821/1099511627776)), (131/1099511627776), by norm_num⟩
  | 10 => ⟨((420094613/2199023255552), (261089087/2199023255552)), (117/4398046511104), by norm_num⟩
  | 11 => ⟨((-671303425/17592186044416), (-208607767/8796093022208)), (3/549755813888), by norm_num⟩
  | 12 => ⟨((15364629/2199023255552), (305572075/70368744177664)), (143/140737488355328), by norm_num⟩
  | _ => zero

def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197806907547143/1267650600228229401496703205376), (362177485687/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1780168476148053/633825300114114700748351602688), (858520118651/633825300114114700748351602688)), (92285/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891316322654777/39614081257132168796771975168), (965734530461/39614081257132168796771975168)), (51913/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((945594782527037/1237940039285380274899124224), (64123168499/154742504910672534362390528)), (110321/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772855549703899/154742504910672534362390528), (1025833196529/154742504910672534362390528)), (13791/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1551113952423523/9671406556917033397649408), (480786276355/4835703278458516698824704)), (6465/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((630076931731713/302231454903657293676544), (420614970867/302231454903657293676544)), (45259/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((472502483707235/18889465931478580854784), (341681221115/18889465931478580854784)), (147105/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299202408965043/4722366482869645213696), (1024804171513/4722366482869645213696)), (110341/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1623733928037199/590295810358705651712), (1408716669703/590295810358705651712)), (151739/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1826330758772425/73786976294838206464), (1760312427059/73786976294838206464)), (189703/73786976294838206464), by norm_num⟩
  | 7 => ⟨((456467122387623/2305843009213693952), (494887399703/2305843009213693952)), (106729/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1597115038549307/1152921504606846976), (989273853711/576460752303423488)), (213509/1152921504606846976), by norm_num⟩
  | 5 => ⟨((299329148224135/36028797018963968), (1730102749275/144115188075855872)), (93439/72057594037927936), by norm_num⟩
  | 4 => ⟨((747868374504711/18014398509481984), (2592902716335/36028797018963968)), (140217/18014398509481984), by norm_num⟩
  | 3 => ⟨((1494374177383681/9007199254740992), (1618595994465/4503599627370496)), (175373/4503599627370496), by norm_num⟩
  | 2 => ⟨((559539510899345/1125899906842624), (3231294486713/2251799813685248)), (702103/4503599627370496), by norm_num⟩
  | 1 => ⟨((278920151645461/281474976710656), (604027852965/140737488355328)), (1054687/2251799813685248), by norm_num⟩
  | 0 => ⟨((2211018757778733/2251799813685248), (19211437800999/2251799813685248)), (2115519/2251799813685248), by norm_num⟩
  | _ => zero

def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((2211018757778733/2251799813685248), (19211437800999/2251799813685248)), (8070064553267668967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1085406180025179/1125899906842624), (1178969403823/70368744177664)), (4190511/2251799813685248), by norm_num⟩
  | 2 => ⟨((2092105588520235/2251799813685248), (18185071965179/562949953421312)), (8220011/2251799813685248), by norm_num⟩
  | 3 => ⟨((970693446520241/1125899906842624), (135163314091335/2251799813685248)), (15805187/2251799813685248), by norm_num⟩
  | 4 => ⟨((832825796546915/1125899906842624), (233061824414477/2251799813685248)), (29150251/2251799813685248), by norm_num⟩
  | 5 => ⟨((1207957030214417/2251799813685248), (10774708878595/70368744177664)), (12289719/562949953421312), by norm_num⟩
  | 6 => ⟨((595203695659981/2251799813685248), (739839000426203/4503599627370496)), (135591687/4503599627370496), by norm_num⟩
  | _ => zero

def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-9791817/8388608), (-64717791/2097152)), (1/16777216), by norm_num⟩, -5, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-1236190959/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-41045403/33554432), (-67821115/2097152)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1236190959/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((99872153869595/562949953421312), (-1057364500983237/4503599627370496)), (160822813/4503599627370496), by norm_num⟩
  | 1 => ⟨((-219310887/536870912), (1160941953/2147483648)), (179/2147483648), by norm_num⟩
  | 2 => ⟨((504981979/1073741824), (-668291909/1073741824)), (105/1073741824), by norm_num⟩
  | 3 => ⟨((-775175985/2147483648), (128233249/268435456)), (41/536870912), by norm_num⟩
  | 4 => ⟨((446227167/2147483648), (-590535935/2147483648)), (3/67108864), by norm_num⟩
  | 5 => ⟨((-410990409/4294967296), (1087807393/8589934592)), (179/8589934592), by norm_num⟩
  | 6 => ⟨((630893593/17179869184), (-834923029/17179869184)), (139/17179869184), by norm_num⟩
  | 7 => ⟨((-415053195/34359738368), (1098560755/68719476736)), (185/68719476736), by norm_num⟩
  | 8 => ⟨((238923825/68719476736), (-632382405/137438953472)), (27/34359738368), by norm_num⟩
  | 9 => ⟨((-122253875/137438953472), (647161911/549755813888)), (113/549755813888), by norm_num⟩
  | 10 => ⟨((900799841/4398046511104), (-1192116295/4398046511104)), (211/4398046511104), by norm_num⟩
  | 11 => ⟨((-754243013/17592186044416), (998163349/17592186044416)), (179/17592186044416), by norm_num⟩
  | 12 => ⟨((289451453/35184372088832), (-766118683/70368744177664)), (139/70368744177664), by norm_num⟩
  | _ => zero

def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395595587393901/2535301200456458802993406410752), (-1203223953723/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((445020343192165/158456325028528675187087900672), (-1425953754235/633825300114114700748351602688)), (23085/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((472804575246681/9903520314283042199192993792), (-1604022477343/39614081257132168796771975168)), (25973/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1891085378580041/2475880078570760549798248448), (-1704061044193/2475880078570760549798248448)), (110395/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886375659996957/77371252455336267181195264), (-106488852335/9671406556917033397649408)), (110407/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1551016191152931/9671406556917033397649408), (-1597078453887/9671406556917033397649408)), (103519/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1260068276457485/604462909807314587353088), (-1397189359459/604462909807314587353088)), (2831/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((944935384971111/37778931862957161709568), (-1134978006003/37778931862957161709568)), (147235/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299097960097689/4722366482869645213696), (-425512497831/1180591620717411303424)), (110447/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405897547183395/147573952589676412928), (-2339641257363/590295810358705651712)), (151897/590295810358705651712), by norm_num⟩
  | 8 => ⟨((456537725409657/18446744073709551616), (-1461767826687/36893488147419103232)), (189921/73786976294838206464), by norm_num⟩
  | 7 => ⟨((912832949453789/4611686018427387904), (-3287581214171/9223372036854775808)), (213729/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1596912134092103/1152921504606846976), (-3285836456879/1152921504606846976)), (26727/144115188075855872), by norm_num⟩
  | 5 => ⟨((74821168687377/9007199254740992), (-718286265409/36028797018963968)), (187185/144115188075855872), by norm_num⟩
  | 4 => ⟨((373867301129995/9007199254740992), (-2152898224899/18014398509481984)), (140485/18014398509481984), by norm_num⟩
  | 3 => ⟨((1494038518444585/9007199254740992), (-1343847315159/2251799813685248)), (351551/9007199254740992), by norm_num⟩
  | 2 => ⟨((2237483052901791/4503599627370496), (-5365116197835/2251799813685248)), (704117/4503599627370496), by norm_num⟩
  | 1 => ⟨((2230339587571127/2251799813685248), (-16044062948651/2251799813685248)), (1058717/2251799813685248), by norm_num⟩
  | 0 => ⟨((552234800678161/562949953421312), (-15941730433717/1125899906842624)), (265953/281474976710656), by norm_num⟩
  | _ => zero

def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((552234800678161/562949953421312), (-15941730433717/1125899906842624)), (1014530182958507449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((2166442956676511/2251799813685248), (-62553186300311/2251799813685248)), (4234505/2251799813685248), by norm_num⟩
  | 2 => ⟨((520645991144091/562949953421312), (-60182041518245/1125899906842624)), (4191623/1125899906842624), by norm_num⟩
  | 3 => ⟨((1919650419524195/2251799813685248), (-13914886423257/140737488355328)), (16402751/2251799813685248), by norm_num⟩
  | 4 => ⟨((403620467354243/562949953421312), (-379596337439193/2251799813685248)), (15605041/1125899906842624), by norm_num⟩
  | 5 => ⟨((1093551172849981/2251799813685248), (-544321391953297/2251799813685248)), (55276091/2251799813685248), by norm_num⟩
  | 6 => ⟨((99872153869595/562949953421312), (-1057364500983237/4503599627370496)), (160822813/4503599627370496), by norm_num⟩
  | _ => zero

def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-41045403/33554432), (-67821115/2097152)), (1/16777216), by norm_num⟩, -5, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-643680111/268435456), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-21372191/16777216), (-1130054609/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-643680111/268435456), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-200856998066523/1125899906842624), (-970429462420673/4503599627370496)), (56418335/1125899906842624), by norm_num⟩
  | 1 => ⟨((918644039/2147483648), (554797225/1073741824)), (261/2147483648), by norm_num⟩
  | 2 => ⟨((-275351525/536870912), (-332586411/536870912)), (159/1073741824), by norm_num⟩
  | 3 => ⟨((27511005/67108864), (1063343177/2147483648)), (1/8388608), by norm_num⟩
  | 4 => ⟨((-527748071/2147483648), (-318723197/1073741824)), (39/536870912), by norm_num⟩
  | 5 => ⟨((253096921/2147483648), (305705939/2147483648)), (151/4294967296), by norm_num⟩
  | 6 => ⟨((-809199881/17179869184), (-977401101/17179869184)), (61/4294967296), by norm_num⟩
  | 7 => ⟨((277196653/17179869184), (669630137/34359738368)), (169/34359738368), by norm_num⟩
  | 8 => ⟨((-20771517/4294967296), (-401425735/68719476736)), (51/34359738368), by norm_num⟩
  | 9 => ⟨((708379341/549755813888), (855623887/549755813888)), (55/137438953472), by norm_num⟩
  | 10 => ⟨((-679447789/2199023255552), (-410339295/1099511627776)), (213/2199023255552), by norm_num⟩
  | 11 => ⟨((592452597/8796093022208), (715600477/8796093022208)), (187/8796093022208), by norm_num⟩
  | 12 => ⟨((-473546427/35184372088832), (-1143956667/70368744177664)), (151/35184372088832), by norm_num⟩
  | _ => zero

def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((12361846826271/79228162514264337593543950336), (-2946931211405/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779997785790449/633825300114114700748351602688), (-3492148699889/633825300114114700748351602688)), (723/4951760157141521099596496896), by norm_num⟩
  | 16 => ⟨((945561978361239/19807040628566084398385987584), (-1964104164129/19807040628566084398385987584)), (104133/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((7386659178019/9671406556917033397649408), (-2086588564797/1237940039285380274899124224)), (110667/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((443162563601907/38685626227668133590597632), (-1043141207897/38685626227668133590597632)), (13837/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((387730244621675/2417851639229258349412352), (-1955564478855/4835703278458516698824704)), (811/75557863725914323419136), by norm_num⟩
  | 12 => ⟨((1259984501904823/604462909807314587353088), (-3421587260121/604462909807314587353088)), (90863/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((236216720966663/9444732965739290427392), (-2779429725829/37778931862957161709568)), (36927/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1298994448895045/4722366482869645213696), (-521009651391/590295810358705651712)), (6927/295147905179352825856), by norm_num⟩
  | 9 => ⟨((1623446627401567/590295810358705651712), (-1432342913489/147573952589676412928)), (152475/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825969601289861/73786976294838206464), (-7159112761475/73786976294838206464)), (190715/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1825459396445005/9223372036854775808), (-4025212155829/4611686018427387904)), (107361/4611686018427387904), by norm_num⟩
  | 6 => ⟨((798351230360293/576460752303423488), (-4022976145179/576460752303423488)), (53733/288230376151711744), by norm_num⟩
  | 5 => ⟨((299237918102525/36028797018963968), (-7035177110569/144115188075855872)), (94151/72057594037927936), by norm_num⟩
  | 4 => ⟨((1495181552068759/36028797018963968), (-2635675773219/9007199254740992)), (282927/36028797018963968), by norm_num⟩
  | 3 => ⟨((746833266666883/4503599627370496), (-13160768755175/9007199254740992)), (44311/1125899906842624), by norm_num⟩
  | 2 => ⟨((1118350966881741/2251799813685248), (-3283588115107/562949953421312)), (355733/2251799813685248), by norm_num⟩
  | 1 => ⟨((1114537710134623/1125899906842624), (-9817742200007/562949953421312)), (268359/562949953421312), by norm_num⟩
  | 0 => ⟨((1103021606609625/1125899906842624), (-39006773472303/1125899906842624)), (1085937/1125899906842624), by norm_num⟩
  | _ => zero

def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((1103021606609625/1125899906842624), (-39006773472303/1125899906842624)), (4142520908835982921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((269814201263809/281474976710656), (-76428310691905/1125899906842624)), (2202987/1125899906842624), by norm_num⟩
  | 2 => ⟨((514678950384181/562949953421312), (-73262084765981/562949953421312)), (4522533/1125899906842624), by norm_num⟩
  | 3 => ⟨((230506359692399/281474976710656), (-66980115481229/281474976710656)), (9446605/1125899906842624), by norm_num⟩
  | 4 => ⟨((172828315174779/281474976710656), (-438812508927941/1125899906842624)), (19967937/1125899906842624), by norm_num⟩
  | 5 => ⟨((126724233962787/562949953421312), (-1077740230863835/2251799813685248)), (40085767/1125899906842624), by norm_num⟩
  | 6 => ⟨((-200856998066523/1125899906842624), (-970429462420673/4503599627370496)), (56418335/1125899906842624), by norm_num⟩
  | _ => zero

def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-21372191/16777216), (-1130054609/33554432)), (1/16777216), by norm_num⟩, -5, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-1334074099/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-44295429/33554432), (-585530203/16777216)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-1334074099/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-35404730546981/140737488355328), (404340162204145/4503599627370496)), (52238875/2251799813685248), by norm_num⟩
  | 1 => ⟨((1342429357/2147483648), (-239550485/1073741824)), (63/1073741824), by norm_num⟩
  | 2 => ⟨((-833952909/1073741824), (37203787/134217728)), (5/67108864), by norm_num⟩
  | 3 => ⟨((690765043/1073741824), (-123263917/536870912)), (135/2147483648), by norm_num⟩
  | 4 => ⟨((-214560831/536870912), (306299327/2147483648)), (85/2147483648), by norm_num⟩
  | 5 => ⟨((853061817/4294967296), (-152225047/2147483648)), (43/2147483648), by norm_num⟩
  | 6 => ⟨((-353296497/4294967296), (504353375/17179869184)), (145/17179869184), by norm_num⟩
  | 7 => ⟨((1003324359/34359738368), (-89519361/8589934592)), (105/34359738368), by norm_num⟩
  | 8 => ⟨((-623291843/68719476736), (444894511/137438953472)), (133/137438953472), by norm_num⟩
  | 9 => ⟨((1376730707/549755813888), (-491342813/549755813888)), (149/549755813888), by norm_num⟩
  | 10 => ⟨((-1368418915/2199023255552), (488376409/2199023255552)), (75/1099511627776), by norm_num⟩
  | 11 => ⟨((77281665/549755813888), (-55162263/1099511627776)), (69/4398046511104), by norm_num⟩
  | 12 => ⟨((-1024201191/35184372088832), (182764099/17592186044416)), (117/35184372088832), by norm_num⟩
  | _ => zero

def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582256180796103/10141204801825835211973625643008), (911434795345/2535301200456458802993406410752)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889961490783531/316912650057057350374175801344), (2159957673557/316912650057057350374175801344)), (46313/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472759902396997/9903520314283042199192993792), (1214827052993/9903520314283042199192993792)), (52115/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945447443735081/1237940039285380274899124224), (5162316301073/2475880078570760549798248448)), (13847/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1772560118728391/154742504910672534362390528), (2580765059661/77371252455336267181195264)), (27703/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1550836185742021/9671406556917033397649408), (4838099087441/9671406556917033397649408)), (25981/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259910017853537/604462909807314587353088), (4232501210581/604462909807314587353088)), (22743/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((236201523370021/9444732965739290427392), (859530965953/9444732965739290427392)), (36975/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298902787458765/4722366482869645213696), (5155814704945/4722366482869645213696)), (55493/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1623319820240597/590295810358705651712), (885877104325/73786976294838206464)), (76353/590295810358705651712), by norm_num⟩
  | 8 => ⟨((456452483581411/18446744073709551616), (4427713917083/36893488147419103232)), (47759/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1825278180493687/9223372036854775808), (9957758377271/9223372036854775808)), (107561/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1596519258975697/1152921504606846976), (9952009427459/1152921504606846976)), (107691/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196789140271921/144115188075855872), (4350769293439/72057594037927936)), (11797/18014398509481984), by norm_num⟩
  | 4 => ⟨((747466650577729/18014398509481984), (6519681675385/18014398509481984)), (141857/36028797018963968), by norm_num⟩
  | 3 => ⟨((746674223310801/4503599627370496), (4069134907247/2251799813685248)), (88917/4503599627370496), by norm_num⟩
  | 2 => ⟨((1118021258899307/2251799813685248), (8121259860823/1125899906842624)), (89303/1125899906842624), by norm_num⟩
  | 1 => ⟨((557007114591655/562949953421312), (24278649962805/1125899906842624)), (16865/70368744177664), by norm_num⟩
  | 0 => ⟨((275464943540605/281474976710656), (12054077356089/281474976710656)), (273713/562949953421312), by norm_num⟩
  | _ => zero

def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((275464943540605/281474976710656), (12054077356089/281474976710656)), (1044132234813499273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((538134048177043/562949953421312), (94373596605497/1125899906842624)), (559181/562949953421312), by norm_num⟩
  | 2 => ⟨((255228424948715/281474976710656), (180426857747105/1125899906842624)), (1162805/562949953421312), by norm_num⟩
  | 3 => ⟨((896803459433513/1125899906842624), (327205375478737/1125899906842624)), (4962875/1125899906842624), by norm_num⟩
  | 4 => ⟨((604718607749/1099511627776), (260626109737825/562949953421312)), (1348833/140737488355328), by norm_num⟩
  | 5 => ⟨((49624399307487/562949953421312), (573365316899783/1125899906842624)), (21860879/1125899906842624), by norm_num⟩
  | 6 => ⟨((-35404730546981/140737488355328), (404340162204145/4503599627370496)), (52238875/2251799813685248), by norm_num⟩
  | _ => zero

def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-44295429/33554432), (-585530203/16777216)), (1/33554432), by norm_num⟩, -6, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-1377046701/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-22861127/16777216), (-1208782083/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1377046701/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-119454813881629/4503599627370496), (8958255469805/35184372088832)), (188748187/4503599627370496), by norm_num⟩
  | 1 => ⟨((73050391/1073741824), (-701216785/1073741824)), (233/2147483648), by norm_num⟩
  | 2 => ⟨((-187370553/2147483648), (899292771/1073741824)), (151/1073741824), by norm_num⟩
  | 3 => ⟨((40049665/536870912), (-1537760277/2147483648)), (65/536870912), by norm_num⟩
  | 4 => ⟨((-102725363/2147483648), (986069309/2147483648)), (169/2147483648), by norm_num⟩
  | 5 => ⟨((52697071/2147483648), (-31615223/134217728)), (11/268435456), by norm_num⟩
  | 6 => ⟨((-180220425/17179869184), (1729950847/17179869184)), (19/1073741824), by norm_num⟩
  | 7 => ⟨((66036609/17179869184), (-316945451/8589934592)), (7/1073741824), by norm_num⟩
  | 8 => ⟨((-84690279/68719476736), (812949031/68719476736)), (289/137438953472), by norm_num⟩
  | 9 => ⟨((24136253/68719476736), (-463371799/137438953472)), (83/137438953472), by norm_num⟩
  | 10 => ⟨((-198106453/2199023255552), (1901640317/2199023255552)), (343/2199023255552), by norm_num⟩
  | 11 => ⟨((184775643/8796093022208), (-1773676767/8796093022208)), (323/8796093022208), by norm_num⟩
  | 12 => ⟨((-19747507/4398046511104), (1516463695/35184372088832)), (139/17592186044416), by norm_num⟩
  | _ => zero

def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582200790233439/10141204801825835211973625643008), (1090675763961/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889931873816743/316912650057057350374175801344), (1292274761087/316912650057057350374175801344)), (46227/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890973355728091/39614081257132168796771975168), (2907261127967/39614081257132168796771975168)), (104027/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236353121904259/309485009821345068724781056), (3088534807409/2475880078570760549798248448)), (27637/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1772490749104601/154742504910672534362390528), (3088050933785/154742504910672534362390528)), (110569/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((48461616500529/302231454903657293676544), (2894533688371/9671406556917033397649408)), (103681/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259854193384659/604462909807314587353088), (19782835747/4722366482869645213696)), (11343/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1889522551728975/75557863725914323419136), (4113866210443/75557863725914323419136)), (36875/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((649418252539703/2361183241434822606848), (3084556614325/4722366482869645213696)), (110663/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811615107508987/295147905179352825856), (264993477479/36893488147419103232)), (152221/590295810358705651712), by norm_num⟩
  | 8 => ⟨((456425056395337/18446744073709551616), (5297815413367/73786976294838206464)), (95183/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1825157914701321/9223372036854775808), (5957218587737/9223372036854775808)), (214287/9223372036854775808), by norm_num⟩
  | 6 => ⟨((798201467251217/576460752303423488), (5953689925407/1152921504606846976)), (107221/576460752303423488), by norm_num⟩
  | 5 => ⟨((598345892171889/72057594037927936), (5205510354083/144115188075855872)), (46953/36028797018963968), by norm_num⟩
  | 4 => ⟨((1494796108239715/36028797018963968), (1950083102181/9007199254740992)), (70517/9007199254740992), by norm_num⟩
  | 3 => ⟨((186649049180629/1125899906842624), (9736540516673/9007199254740992)), (176599/4503599627370496), by norm_num⟩
  | 2 => ⟨((279472073797853/562949953421312), (1214467997979/281474976710656)), (354119/2251799813685248), by norm_num⟩
  | 1 => ⟨((1113872271093323/1125899906842624), (7260840290837/562949953421312)), (533485/1125899906842624), by norm_num⟩
  | 0 => ⟨((275451097656557/281474976710656), (14417977939107/562949953421312)), (1076217/1125899906842624), by norm_num⟩
  | _ => zero

def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((275451097656557/281474976710656), (14417977939107/562949953421312)), (4105442051414107921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1077486014057725/1125899906842624), (28218834197809/562949953421312)), (1080749/562949953421312), by norm_num⟩
  | 2 => ⟨((514162445986375/562949953421312), (6751354848767/70368744177664)), (4353805/1125899906842624), by norm_num⟩
  | 3 => ⟨((464421124057207/562949953421312), (197320168965917/1125899906842624)), (8788405/1125899906842624), by norm_num⟩
  | 4 => ⟨((731692637857773/1125899906842624), (651138909335523/2251799813685248)), (35161817/2251799813685248), by norm_num⟩
  | 5 => ⟨((762729695371793/2251799813685248), (423157994141425/1125899906842624)), (33018261/1125899906842624), by norm_num⟩
  | 6 => ⟨((-119454813881629/4503599627370496), (8958255469805/35184372088832)), (188748187/4503599627370496), by norm_num⟩
  | _ => zero

def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-22861127/16777216), (-1208782083/33554432)), (1/16777216), by norm_num⟩, -6, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-1416833115/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-47043287/33554432), (-1243706901/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1416833115/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((111640248162267/562949953421312), (656342917538689/4503599627370496)), (56715759/2251799813685248), by norm_num⟩
  | 1 => ⟨((-140488155/268435456), (-825942319/2147483648)), (145/2147483648), by norm_num⟩
  | 2 => ⟨((370756295/536870912), (544927283/1073741824)), (49/536870912), by norm_num⟩
  | 3 => ⟨((-326149039/536870912), (-119841195/268435456)), (11/134217728), by norm_num⟩
  | 4 => ⟨((215181503/536870912), (39533473/134217728)), (59/1073741824), by norm_num⟩
  | 5 => ⟨((-227150529/1073741824), (-667719051/4294967296)), (127/4294967296), by norm_num⟩
  | 6 => ⟨((399642179/4294967296), (73422869/1073741824)), (57/4294967296), by norm_num⟩
  | 7 => ⟨((-301336749/8589934592), (-442896367/17179869184)), (87/17179869184), by norm_num⟩
  | 8 => ⟨((198811239/17179869184), (146103613/17179869184)), (117/68719476736), by norm_num⟩
  | 9 => ⟨((-932754235/274877906944), (-171367027/68719476736)), (139/274877906944), by norm_num⟩
  | 10 => ⟨((123079595/137438953472), (361797927/549755813888)), (149/1099511627776), by norm_num⟩
  | 11 => ⟨((-472456883/2199023255552), (-694403979/4398046511104)), (145/4398046511104), by norm_num⟩
  | 12 => ⟨((12987925/274877906944), (610857303/17592186044416)), (65/8796093022208), by norm_num⟩
  | _ => zero

def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395537376651597/2535301200456458802993406410752), (206385081191/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779806043126711/633825300114114700748351602688), (489034287673/316912650057057350374175801344)), (92297/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((118181789088149/2475880078570760549798248448), (1100190188563/39614081257132168796771975168)), (103839/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890756434856085/2475880078570760549798248448), (584392416717/1237940039285380274899124224)), (110337/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772422473640345/154742504910672534362390528), (1168596726411/154742504910672534362390528)), (110345/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387677000281333/2417851639229258349412352), (1095359607269/9671406556917033397649408)), (103457/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259798713581649/604462909807314587353088), (479119938793/302231454903657293676544)), (90533/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944716462037955/37778931862957161709568), (778382655703/37778931862957161709568)), (36783/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((40586554537941/147573952589676412928), (1167246400597/4722366482869645213696)), (27591/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((405784792152693/147573952589676412928), (200553957191/73786976294838206464)), (151773/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825587539285485/73786976294838206464), (2004741670137/73786976294838206464)), (94875/36893488147419103232), by norm_num⟩
  | 7 => ⟨((456258170878787/2305843009213693952), (281779721581/1152921504606846976)), (213515/9223372036854775808), by norm_num⟩
  | 6 => ⟨((99767476703127/72057594037927936), (1126433888743/576460752303423488)), (106787/576460752303423488), by norm_num⟩
  | 5 => ⟨((1196586051918261/144115188075855872), (492429777201/36028797018963968)), (2921/2251799813685248), by norm_num⟩
  | 4 => ⟨((373660456233851/9007199254740992), (2951500888583/36028797018963968)), (70137/9007199254740992), by norm_num⟩
  | 3 => ⟨((373251768569003/2251799813685248), (1841997945787/4503599627370496)), (175459/4503599627370496), by norm_num⟩
  | 2 => ⟨((2235428489521679/4503599627370496), (3675937323479/2251799813685248)), (702533/4503599627370496), by norm_num⟩
  | 1 => ⟨((1113639249522295/1125899906842624), (10987601344417/2251799813685248)), (527775/1125899906842624), by norm_num⟩
  | 0 => ⟨((1101449858685819/1125899906842624), (5453713148113/562949953421312)), (529531/562949953421312), by norm_num⟩
  | _ => zero

def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((1101449858685819/1125899906842624), (5453713148113/562949953421312)), (2020000459911155523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2154850199166353/2251799813685248), (42682242283135/2251799813685248)), (4185295/2251799813685248), by norm_num⟩
  | 2 => ⟨((2061265650184365/2251799813685248), (40844589170721/1125899906842624)), (8168863/2251799813685248), by norm_num⟩
  | 3 => ⟨((235486239329001/281474976710656), (149554233270343/2251799813685248)), (3887003/562949953421312), by norm_num⟩
  | 4 => ⟨((1566158199467755/2251799813685248), (125119342330625/1125899906842624)), (14040331/1125899906842624), by norm_num⟩
  | 5 => ⟨((1061476287515667/2251799813685248), (348088995677503/2251799813685248)), (45302099/2251799813685248), by norm_num⟩
  | 6 => ⟨((111640248162267/562949953421312), (656342917538689/4503599627370496)), (56715759/2251799813685248), by norm_num⟩
  | _ => zero

def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47043287/33554432), (-1243706901/33554432)), (1/16777216), by norm_num⟩, -6, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-1453873381/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-12068285/8388608), (-159527641/4194304)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1453873381/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((252246684927777/1125899906842624), (-351522983462119/4503599627370496)), (22001541/1125899906842624), by norm_num⟩
  | 1 => ⟨((-651451765/1073741824), (28370079/134217728)), (29/536870912), by norm_num⟩
  | 2 => ⟨((882082041/1073741824), (-307310393/1073741824)), (81/1073741824), by norm_num⟩
  | 3 => ⟨((-49765051/67108864), (554807981/2147483648)), (37/536870912), by norm_num⟩
  | 4 => ⟨((1078130051/2147483648), (-187805983/1073741824)), (51/1073741824), by norm_num⟩
  | 5 => ⟨((-145981515/536870912), (50858803/536870912)), (113/4294967296), by norm_num⟩
  | 6 => ⟨((1054200723/8589934592), (-183637589/4294967296)), (13/1073741824), by norm_num⟩
  | 7 => ⟨((-6372385/134217728), (35521415/2147483648)), (41/8589934592), by norm_num⟩
  | 8 => ⟨((1104431263/68719476736), (-96193775/17179869184)), (113/68719476736), by norm_num⟩
  | 9 => ⟨((-41539657/8589934592), (231553397/137438953472)), (69/137438953472), by norm_num⟩
  | 10 => ⟨((1439890899/1099511627776), (-501646579/1099511627776)), (19/137438953472), by norm_num⟩
  | 11 => ⟨((-1417926123/4398046511104), (493994225/4398046511104)), (19/549755813888), by norm_num⟩
  | 12 => ⟨((639969187/8796093022208), (-445920387/17592186044416)), (139/17592186044416), by norm_num⟩
  | _ => zero

def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582101762664655/10141204801825835211973625643008), (-218344840545/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((111234365475375/39614081257132168796771975168), (-517341956561/633825300114114700748351602688)), (92251/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890845434953607/39614081257132168796771975168), (-581935550207/39614081257132168796771975168)), (51893/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1890689331918503/2475880078570760549798248448), (-618215765541/2475880078570760549798248448)), (110277/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886177706111445/77371252455336267181195264), (-154528422139/38685626227668133590597632)), (13785/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((775322587572639/4835703278458516698824704), (-144843287417/2417851639229258349412352)), (103393/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157467973116193/75557863725914323419136), (-253421549489/302231454903657293676544)), (90473/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((118083984226753/4722366482869645213696), (-411708414389/37778931862957161709568)), (147027/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298702935124547/4722366482869645213696), (-617384871413/4722366482869645213696)), (55139/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1623047422064819/590295810358705651712), (-424307729573/295147905179352825856)), (37911/147573952589676412928), by norm_num⟩
  | 8 => ⟨((912736515983001/36893488147419103232), (-530168199499/36893488147419103232)), (189573/73786976294838206464), by norm_num⟩
  | 7 => ⟨((228113013048087/1152921504606846976), (-1192283475359/9223372036854775808)), (106647/4611686018427387904), by norm_num⟩
  | 6 => ⟨((12469932420417/9007199254740992), (-595770102811/576460752303423488)), (106663/576460752303423488), by norm_num⟩
  | 5 => ⟨((1196474148139241/144115188075855872), (-520881057951/72057594037927936)), (186695/144115188075855872), by norm_num⟩
  | 4 => ⟨((1494474646155471/36028797018963968), (-780486790351/18014398509481984)), (280113/36028797018963968), by norm_num⟩
  | 3 => ⟨((1492799282957413/9007199254740992), (-1948298638031/9007199254740992)), (350265/9007199254740992), by norm_num⟩
  | 2 => ⟨((2235016443774347/4503599627370496), (-1943928023303/2251799813685248)), (700901/4503599627370496), by norm_num⟩
  | 1 => ⟨((2226669239192585/2251799813685248), (-5809979166037/2251799813685248)), (526143/1125899906842624), by norm_num⟩
  | 0 => ⟨((2201716232577637/2251799813685248), (-11533027139783/2251799813685248)), (1054163/1125899906842624), by norm_num⟩
  | _ => zero

def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((2201716232577637/2251799813685248), (-11533027139783/2251799813685248)), (4021312717918014171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2152687520720445/2251799813685248), (-22553028835065/2251799813685248)), (259029/140737488355328), by norm_num⟩
  | 2 => ⟨((128606984027721/140737488355328), (-21560364039749/1125899906842624)), (1000889/281474976710656), by norm_num⟩
  | 3 => ⟨((117470428552001/140737488355328), (-39404048290121/1125899906842624)), (1867573/281474976710656), by norm_num⟩
  | 4 => ⟨((783020423937017/1125899906842624), (-131558705314895/2251799813685248)), (25986919/2251799813685248), by norm_num⟩
  | 5 => ⟨((1081435494161683/2251799813685248), (-22873514906213/281474976710656)), (39182331/2251799813685248), by norm_num⟩
  | 6 => ⟨((252246684927777/1125899906842624), (-351522983462119/4503599627370496)), (22001541/1125899906842624), by norm_num⟩
  | _ => zero

def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-12068285/8388608), (-159527641/4194304)), (1/16777216), by norm_num⟩, -6, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨39,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 12 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨39,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 12 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨39,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 12 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨39,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 12 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨39,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 12 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨39,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 12 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨39,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiRectangle.Tile039Terms1
