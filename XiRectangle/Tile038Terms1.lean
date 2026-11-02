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
namespace Reinmann.XiRectangle.Tile038Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨38,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((9/16), (35673/2560)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((9/16), (35673/2560))
  have he : value ((9/16), (35673/2560))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-82942451/67108864), (-2054726415/67108864)), (3/67108864), by norm_num⟩
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
  | 0 => ⟨((913458402913559/4503599627370496), (936995321624381/4503599627370496)), (110991859/4503599627370496), by norm_num⟩
  | 1 => ⟨((-957047107/2147483648), (-30678349/67108864)), (119/2147483648), by norm_num⟩
  | 2 => ⟨((1051423713/2147483648), (1078515559/2147483648)), (133/2147483648), by norm_num⟩
  | 3 => ⟨((-770071341/2147483648), (-789913631/2147483648)), (25/536870912), by norm_num⟩
  | 4 => ⟨((846009839/4294967296), (433904411/2147483648)), (7/268435456), by norm_num⟩
  | 5 => ⟨((-743549445/8589934592), (-762708349/8589934592)), (101/8589934592), by norm_num⟩
  | 6 => ⟨((544581705/17179869184), (558613843/17179869184)), (19/4294967296), by norm_num⟩
  | 7 => ⟨((-341876659/34359738368), (-350685733/34359738368)), (97/68719476736), by norm_num⟩
  | 8 => ⟨((375589899/137438953472), (48158457/17179869184)), (109/274877906944), by norm_num⟩
  | 9 => ⟨((-366780159/549755813888), (-376230917/549755813888)), (109/1099511627776), by norm_num⟩
  | 10 => ⟨((40294919/274877906944), (330665527/2199023255552)), (49/2199023255552), by norm_num⟩
  | 11 => ⟨((-1030248569/35184372088832), (-1056794797/35184372088832)), (159/35184372088832), by norm_num⟩
  | 12 => ⟨((188640623/35184372088832), (774005167/140737488355328)), (119/140737488355328), by norm_num⟩
  | _ => zero

def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582365818783201/10141204801825835211973625643008), (519818262257/5070602400912917605986812821504)), (7279/1267650600228229401496703205376), by norm_num⟩
  | 17 => ⟨((1780062057218433/633825300114114700748351602688), (308014687379/158456325028528675187087900672)), (34621/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((945598294819217/19807040628566084398385987584), (1385913153753/39614081257132168796771975168)), (38951/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1891062333507545/2475880078570760549798248448), (368086737373/618970019642690137449562112)), (41389/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((886364150525511/77371252455336267181195264), (736068992819/77371252455336267181195264)), (82785/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550994638647193/9671406556917033397649408), (1379907373631/9671406556917033397649408)), (77619/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((78753090359845/37778931862957161709568), (603598502367/302231454903657293676544)), (67925/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472460055512353/18889465931478580854784), (980639534101/37778931862957161709568)), (110393/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324768773662683/1180591620717411303424), (1470595331201/4722366482869645213696)), (82809/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1623558822594617/590295810358705651712), (2021477291347/590295810358705651712)), (113883/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1826111804666559/73786976294838206464), (2525959964231/73786976294838206464)), (142385/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1825622066908123/9223372036854775808), (2840486276837/9223372036854775808)), (40057/2305843009213693952), by norm_num⟩
  | 6 => ⟨((798434246014735/576460752303423488), (2838963614099/1152921504606846976)), (160283/1152921504606846976), by norm_num⟩
  | 5 => ⟨((598550362811839/72057594037927936), (2482381116385/144115188075855872)), (140311/144115188075855872), by norm_num⟩
  | 4 => ⟨((747706335349339/18014398509481984), (116254686113/1125899906842624)), (210591/36028797018963968), by norm_num⟩
  | 3 => ⟨((1493968595693249/9007199254740992), (1161051193087/2251799813685248)), (263457/9007199254740992), by norm_num⟩
  | 2 => ⟨((559336358850397/1125899906842624), (9270482856677/4503599627370496)), (131893/1125899906842624), by norm_num⟩
  | 1 => ⟨((1115069355925833/1125899906842624), (13860982144791/2251799813685248)), (396503/1125899906842624), by norm_num⟩
  | 0 => ⟨((1104279768398815/1125899906842624), (6885860662125/562949953421312)), (398155/562949953421312), by norm_num⟩
  | _ => zero

def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((1104279768398815/1125899906842624), (6885860662125/562949953421312)), (1518840791942405523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((541453169672005/562949953421312), (54029077156755/2251799813685248)), (3163037/2251799813685248), by norm_num⟩
  | 2 => ⟨((2081812685789049/2251799813685248), (25982962520191/562949953421312)), (3118147/1125899906842624), by norm_num⟩
  | 3 => ⟨((479965204164379/562949953421312), (96086091952179/1125899906842624)), (12106713/2251799813685248), by norm_num⟩
  | 4 => ⟨((1620452841719763/2251799813685248), (327687962035731/2251799813685248)), (11355263/1125899906842624), by norm_num⟩
  | 5 => ⟨((279608337791451/562949953421312), (471625307055275/2251799813685248)), (39295947/2251799813685248), by norm_num⟩
  | 6 => ⟨((913458402913559/4503599627370496), (936995321624381/4503599627370496)), (110991859/4503599627370496), by norm_num⟩
  | _ => zero

def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-82942451/67108864), (-2054726415/67108864)), (3/67108864), by norm_num⟩, -5, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-21729919/16777216), (-1076626955/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((966623627901969/4503599627370496), (-765901396548071/4503599627370496)), (16127339/562949953421312), by norm_num⟩
  | 1 => ⟨((-1061312273/2147483648), (840927667/2147483648)), (9/134217728), by norm_num⟩
  | 2 => ⟨((610940455/1073741824), (-242038439/536870912)), (85/1073741824), by norm_num⟩
  | 3 => ⟨((-29307133/67108864), (743085469/2147483648)), (133/2147483648), by norm_num⟩
  | 4 => ⟨((1079714681/4294967296), (-427754381/2147483648)), (155/4294967296), by norm_num⟩
  | 5 => ⟨((-248613493/2147483648), (787952689/8589934592)), (145/8589934592), by norm_num⟩
  | 6 => ⟨((763271631/17179869184), (-604776039/17179869184)), (57/8589934592), by norm_num⟩
  | 7 => ⟨((-1004284503/68719476736), (795741881/68719476736)), (153/68719476736), by norm_num⟩
  | 8 => ⟨((1156225263/274877906944), (-916131697/274877906944)), (179/274877906944), by norm_num⟩
  | 9 => ⟨((-295811895/274877906944), (937542751/1099511627776)), (93/549755813888), by norm_num⟩
  | 10 => ⟨((34056603/137438953472), (-863508785/4398046511104)), (87/2199023255552), by norm_num⟩
  | 11 => ⟨((-456251499/8796093022208), (723019075/17592186044416)), (37/4398046511104), by norm_num⟩
  | 12 => ⟨((350185967/35184372088832), (-34683603/4398046511104)), (29/17592186044416), by norm_num⟩
  | _ => zero

def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((49446519348467/316912650057057350374175801344), (-436412071857/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444992703162053/158456325028528675187087900672), (-258567672835/158456325028528675187087900672)), (46151/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((945546982625415/19807040628566084398385987584), (-1163420344463/39614081257132168796771975168)), (51923/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1890953326871117/2475880078570760549798248448), (-154496339285/309485009821345068724781056)), (13793/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((443154832537837/38685626227668133590597632), (-1235786922017/154742504910672534362390528)), (110353/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387723129097175/2417851639229258349412352), (-1158354995383/9671406556917033397649408)), (12933/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1259960126729647/604462909807314587353088), (-506682708315/302231454903657293676544)), (22635/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1889695149757463/75557863725914323419136), (-823176439101/37778931862957161709568)), (147145/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649483176322173/2361183241434822606848), (-1234444559585/4722366482869645213696)), (55187/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1623409403384923/590295810358705651712), (-848420633211/295147905179352825856)), (37947/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1825925182147001/73786976294838206464), (-1060135927445/36893488147419103232)), (189771/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1825412324744203/9223372036854775808), (-1192117079755/4611686018427387904)), (106771/4611686018427387904), by norm_num⟩
  | 6 => ⟨((798329504940679/576460752303423488), (-2327046129/1125899906842624)), (53401/288230376151711744), by norm_num⟩
  | 5 => ⟨((1196917720990579/144115188075855872), (-2083527967853/144115188075855872)), (93487/72057594037927936), by norm_num⟩
  | 4 => ⟨((747569373782165/18014398509481984), (-390285441965/4503599627370496)), (280601/36028797018963968), by norm_num⟩
  | 3 => ⟨((1493627211928675/9007199254740992), (-487199361055/1125899906842624)), (87749/2251799813685248), by norm_num⟩
  | 2 => ⟨((2236665722245901/4503599627370496), (-7779431952023/4503599627370496)), (702729/4503599627370496), by norm_num⟩
  | 1 => ⟨((2229126756780221/2251799813685248), (-5814912986017/1125899906842624)), (1055941/2251799813685248), by norm_num⟩
  | 0 => ⟨((275820744740795/281474976710656), (-23102799081087/2251799813685248)), (2119293/2251799813685248), by norm_num⟩
  | _ => zero

def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((275820744740795/281474976710656), (-23102799081087/2251799813685248)), (8084461220748137717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1081001862991225/1125899906842624), (-45277426239511/2251799813685248)), (2098465/1125899906842624), by norm_num⟩
  | 2 => ⟨((2074878076390229/2251799813685248), (-43471876868359/1125899906842624)), (8227913/2251799813685248), by norm_num⟩
  | 3 => ⟨((477124985695075/562949953421312), (-160225333896047/2251799813685248)), (15798281/2251799813685248), by norm_num⟩
  | 4 => ⟨((1606137389296295/2251799813685248), (-135798057497887/1125899906842624)), (14513859/1125899906842624), by norm_num⟩
  | 5 => ⟨((1112848863555769/2251799813685248), (-387441789835145/2251799813685248)), (48411337/2251799813685248), by norm_num⟩
  | 6 => ⟨((966623627901969/4503599627370496), (-765901396548071/4503599627370496)), (16127339/562949953421312), by norm_num⟩
  | _ => zero

def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-21729919/16777216), (-1076626955/33554432)), (1/16777216), by norm_num⟩, -5, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-22629379/16777216), (-280297859/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-484499942609533/4503599627370496), (-1063757913896103/4503599627370496)), (204315243/4503599627370496), by norm_num⟩
  | 1 => ⟨((138494983/536870912), (1216306721/2147483648)), (59/536870912), by norm_num⟩
  | 2 => ⟨((-332096465/1073741824), (-364572017/536870912)), (285/2147483648), by norm_num⟩
  | 3 => ⟨((265444181/1073741824), (1165607355/2147483648)), (115/1073741824), by norm_num⟩
  | 4 => ⟨((-636507347/4294967296), (-1397502183/4294967296)), (139/2147483648), by norm_num⟩
  | 5 => ⟨((610511183/8589934592), (1340425551/8589934592)), (269/8589934592), by norm_num⟩
  | 6 => ⟨((-487980627/17179869184), (-1071400031/17179869184)), (217/17179869184), by norm_num⟩
  | 7 => ⟨((668643679/68719476736), (183507505/8589934592)), (75/17179869184), by norm_num⟩
  | 8 => ⟨((-400834379/137438953472), (-440031779/68719476736)), (91/68719476736), by norm_num⟩
  | 9 => ⟨((427181717/549755813888), (234477805/137438953472)), (49/137438953472), by norm_num⟩
  | 10 => ⟨((-51216851/274877906944), (-28112661/68719476736)), (95/1099511627776), by norm_num⟩
  | 11 => ⟨((357273149/8796093022208), (784421433/8796093022208)), (167/8796093022208), by norm_num⟩
  | 12 => ⟨((-285567865/35184372088832), (-1253973631/70368744177664)), (269/70368744177664), by norm_num⟩
  | _ => zero

def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582218783543223/10141204801825835211973625643008), (-1301427640481/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889941777618505/316912650057057350374175801344), (-1542016833715/316912650057057350374175801344)), (11563/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1890995547740645/39614081257132168796771975168), (-1734556475839/19807040628566084398385987584)), (52043/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1890848439242045/2475880078570760549798248448), (-1842712038909/1237940039285380274899124224)), (110613/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((443128520945699/38685626227668133590597632), (-3684852091981/154742504910672534362390528)), (110639/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775396733459855/4835703278458516698824704), (-1726970567883/4835703278458516698824704)), (103751/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259873077628249/604462909807314587353088), (-1510795416037/302231454903657293676544)), (90809/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472388245331305/18889465931478580854784), (-2454472909413/37778931862957161709568)), (147615/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649429551135241/2361183241434822606848), (-3680712573781/4722366482869645213696)), (27689/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1623260920766425/590295810358705651712), (-5059360159649/590295810358705651712)), (19045/73786976294838206464), by norm_num⟩
  | 8 => ⟨((456434515028195/18446744073709551616), (-6321771027331/73786976294838206464)), (95279/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1825199726222981/9223372036854775808), (-1777163184087/2305843009213693952)), (107263/4611686018427387904), by norm_num⟩
  | 6 => ⟨((49888868958231/36028797018963968), (-7104478814753/1152921504606846976)), (26839/144115188075855872), by norm_num⟩
  | 5 => ⟨((598363246071515/72057594037927936), (-1552931054545/36028797018963968)), (94041/72057594037927936), by norm_num⟩
  | 4 => ⟨((1494846062851963/36028797018963968), (-2327049784477/9007199254740992)), (282541/36028797018963968), by norm_num⟩
  | 3 => ⟨((373312789349231/2251799813685248), (-11618826536611/9007199254740992)), (88477/2251799813685248), by norm_num⟩
  | 2 => ⟨((558970778169705/1125899906842624), (-11594203400059/2251799813685248)), (5547/35184372088832), by norm_num⟩
  | 1 => ⟨((1113938462341619/1125899906842624), (-8664892017269/562949953421312)), (535265/1125899906842624), by norm_num⟩
  | 0 => ⟨((275470577519041/281474976710656), (-17206853141979/562949953421312)), (1081569/1125899906842624), by norm_num⟩
  | _ => zero

def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((275470577519041/281474976710656), (-17206853141979/562949953421312)), (4125858311179732921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1077325182022713/1125899906842624), (-33679596159475/562949953421312)), (2183113/1125899906842624), by norm_num⟩
  | 2 => ⟨((1026816220522173/1125899906842624), (-64453113180743/562949953421312)), (4439073/1125899906842624), by norm_num⟩
  | 3 => ⟨((14401462460521/17592186044416), (-235123927713013/1125899906842624)), (9113309/1125899906842624), by norm_num⟩
  | 4 => ⟨((705423121019209/1125899906842624), (-769916464043765/2251799813685248)), (2340891/140737488355328), by norm_num⟩
  | 5 => ⟨((620710486151431/2251799813685248), (-964769375481869/2251799813685248)), (72545389/2251799813685248), by norm_num⟩
  | 6 => ⟨((-484499942609533/4503599627370496), (-1063757913896103/4503599627370496)), (204315243/4503599627370496), by norm_num⟩
  | _ => zero

def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-22629379/16777216), (-280297859/8388608)), (1/16777216), by norm_num⟩, -5, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-46901043/33554432), (-580937809/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-555205147600671/2251799813685248), (38410541961977/2251799813685248)), (181242535/4503599627370496), by norm_num⟩
  | 1 => ⟨((1315720523/2147483648), (-45512491/1073741824)), (217/2147483648), by norm_num⟩
  | 2 => ⟨((-817360669/1073741824), (28273573/536870912)), (17/134217728), by norm_num⟩
  | 3 => ⟨((1354043307/2147483648), (-93676253/2147483648)), (57/536870912), by norm_num⟩
  | 4 => ⟨((-210291951/536870912), (29097093/1073741824)), (143/2147483648), by norm_num⟩
  | 5 => ⟨((1672178775/8589934592), (-1807589/134217728)), (287/8589934592), by norm_num⟩
  | 6 => ⟨((-692534693/8589934592), (47911359/8589934592)), (15/1073741824), by norm_num⟩
  | 7 => ⟨((491681161/17179869184), (-34015787/17179869184)), (343/68719476736), by norm_num⟩
  | 8 => ⟨((-610890893/68719476736), (84526055/137438953472)), (215/137438953472), by norm_num⟩
  | 9 => ⟨((1349339415/549755813888), (-93350825/549755813888)), (239/549755813888), by norm_num⟩
  | 10 => ⟨((-670596497/1099511627776), (46393617/1099511627776)), (15/137438953472), by norm_num⟩
  | 11 => ⟨((75744077/549755813888), (-83842769/8796093022208)), (219/8796093022208), by norm_num⟩
  | 12 => ⟨((-2007647579/70368744177664), (138894303/70368744177664)), (183/35184372088832), by norm_num⟩
  | _ => zero

def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791077514319855/5070602400912917605986812821504), (4002300480255/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((55618783982479/19807040628566084398385987584), (2370902769981/316912650057057350374175801344)), (92667/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890902377802147/39614081257132168796771975168), (83341166853/618970019642690137449562112)), (13035/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1890748948152275/2475880078570760549798248448), (5666386859491/2475880078570760549798248448)), (6927/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((886207016312957/77371252455336267181195264), (1416368139721/38685626227668133590597632)), (110871/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((48459346067381/302231454903657293676544), (1327602239175/2417851639229258349412352)), (103983/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629894944728311/302231454903657293676544), (4645636131605/604462909807314587353088)), (45513/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1889416686490531/75557863725914323419136), (7547336472781/75557863725914323419136)), (147995/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324688976746007/1180591620717411303424), (5658907600999/4722366482869645213696)), (111065/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1623117445433859/590295810358705651712), (3889202964689/295147905179352825856)), (152825/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912778172660715/36893488147419103232), (4859559211661/36893488147419103232)), (191197/73786976294838206464), by norm_num⟩
  | 7 => ⟨((912496020438425/4611686018427387904), (5464329659741/4611686018427387904)), (53831/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1596232056166859/1152921504606846976), (5460985436463/576460752303423488)), (215611/1152921504606846976), by norm_num⟩
  | 5 => ⟨((598268322093457/72057594037927936), (4774598422311/72057594037927936)), (188981/144115188075855872), by norm_num⟩
  | 4 => ⟨((1494552175932409/36028797018963968), (447147876645/1125899906842624)), (284115/36028797018963968), by norm_num⟩
  | 3 => ⟨((373216971758117/2251799813685248), (8929768416475/4503599627370496)), (356271/9007199254740992), by norm_num⟩
  | 2 => ⟨((34922953044719/70368744177664), (17819934550121/2251799813685248)), (178983/1125899906842624), by norm_num⟩
  | 1 => ⟨((556634339630351/562949953421312), (13315387559283/562949953421312)), (541193/1125899906842624), by norm_num⟩
  | 0 => ⟨((550153812599299/562949953421312), (6608040942489/140737488355328)), (137427/140737488355328), by norm_num⟩
  | _ => zero

def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((550153812599299/562949953421312), (6608040942489/140737488355328)), (524242401659917787/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((1072814932839999/1125899906842624), (103325388588547/1125899906842624)), (1126047/562949953421312), by norm_num⟩
  | 2 => ⟨((1012750544935341/1125899906842624), (24613426812101/140737488355328)), (4705177/1125899906842624), by norm_num⟩
  | 3 => ⟨((876535409928725/1125899906842624), (2767481956565/8796093022208)), (10110411/1125899906842624), by norm_num⟩
  | 4 => ⟨((1141895437815823/2251799813685248), (551562136767655/1125899906842624)), (44208627/2251799813685248), by norm_num⟩
  | 5 => ⟨((38654425456823/2251799813685248), (559398116847849/1125899906842624)), (44075517/1125899906842624), by norm_num⟩
  | 6 => ⟨((-555205147600671/2251799813685248), (38410541961977/2251799813685248)), (181242535/4503599627370496), by norm_num⟩
  | _ => zero

def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-46901043/33554432), (-580937809/16777216)), (1/16777216), by norm_num⟩, -6, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-24205899/16777216), (-18739085/524288)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-400946300277329/4503599627370496), (985631001427827/4503599627370496)), (92551453/2251799813685248), by norm_num⟩
  | 1 => ⟨((245191325/1073741824), (-602744485/1073741824)), (57/536870912), by norm_num⟩
  | 2 => ⟨((-157225833/536870912), (193251135/268435456)), (37/268435456), by norm_num⟩
  | 3 => ⟨((537701733/2147483648), (-660905833/1073741824)), (1/8388608), by norm_num⟩
  | 4 => ⟨((-344794429/2147483648), (211898749/536870912)), (83/1073741824), by norm_num⟩
  | 5 => ⟨((88438025/1073741824), (-13587739/67108864)), (43/1073741824), by norm_num⟩
  | 6 => ⟨((-151226037/4294967296), (1487012797/17179869184)), (297/17179869184), by norm_num⟩
  | 7 => ⟨((443299573/34359738368), (-544873217/17179869184)), (219/34359738368), by norm_num⟩
  | 8 => ⟨((-284260239/68719476736), (87348263/8589934592)), (283/137438953472), by norm_num⟩
  | 9 => ⟨((162025137/137438953472), (-796600431/274877906944)), (41/68719476736), by norm_num⟩
  | 10 => ⟨((-332469017/1099511627776), (408647953/549755813888)), (85/549755813888), by norm_num⟩
  | 11 => ⟨((310096797/4398046511104), (-1524598261/8796093022208)), (5/137438953472), by norm_num⟩
  | 12 => ⟨((-265127527/17592186044416), (1303505777/35184372088832)), (69/8796093022208), by norm_num⟩
  | _ => zero

def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395524094960727/2535301200456458802993406410752), (1274699085035/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779738741021083/633825300114114700748351602688), (755056570549/158456325028528675187087900672)), (46249/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890832665351789/39614081257132168796771975168), (424663929369/4951760157141521099596496896)), (52039/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((945337708385069/1237940039285380274899124224), (1804555483281/1237940039285380274899124224)), (110605/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772341106389339/154742504910672534362390528), (3608512002649/154742504910672534362390528)), (55315/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((775315674253797/4835703278458516698824704), (1691171829215/4835703278458516698824704)), (51871/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259731271910107/604462909807314587353088), (2958914419003/604462909807314587353088)), (90801/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889322636827779/75557863725914323419136), (300440189599/4722366482869645213696)), (9225/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((1298686422463779/4722366482869645213696), (1802119310915/2361183241434822606848)), (110743/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1623023613695317/590295810358705651712), (4954132415587/590295810358705651712)), (152343/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825441617755775/73786976294838206464), (1547530604617/18446744073709551616)), (95267/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1824866491837995/9223372036854775808), (3480195830723/4611686018427387904)), (6703/288230376151711744), by norm_num⟩
  | 6 => ⟨((1596110901330007/1152921504606846976), (6956022645415/1152921504606846976)), (214679/1152921504606846976), by norm_num⟩
  | 5 => ⟨((299108892528825/36028797018963968), (6081606128715/144115188075855872)), (11753/9007199254740992), by norm_num⟩
  | 4 => ⟨((1494410419976735/36028797018963968), (2278146367449/9007199254740992)), (141241/18014398509481984), by norm_num⟩
  | 3 => ⟨((373176974709755/2251799813685248), (11373548548341/9007199254740992)), (353819/9007199254740992), by norm_num⟩
  | 2 => ⟨((279350059953981/562949953421312), (11347790111315/2251799813685248)), (22181/140737488355328), by norm_num⟩
  | 1 => ⟨((1113131340779407/1125899906842624), (16957347002959/1125899906842624)), (267521/562949953421312), by norm_num⟩
  | 0 => ⟨((275071867079095/281474976710656), (33657690446561/1125899906842624)), (540451/562949953421312), by norm_num⟩
  | _ => zero

def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((275071867079095/281474976710656), (33657690446561/1125899906842624)), (2061656954051780523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1074251508022315/1125899906842624), (16446015665227/281474976710656)), (2177253/1125899906842624), by norm_num⟩
  | 2 => ⟨((510564372818953/562949953421312), (15691587699721/140737488355328)), (2204589/562949953421312), by norm_num⟩
  | 3 => ⟨((912110792226181/1125899906842624), (227702390487867/1125899906842624)), (8980967/1125899906842624), by norm_num⟩
  | 4 => ⟨((692865958972517/1125899906842624), (737862421046329/2251799813685248)), (18183899/1125899906842624), by norm_num⟩
  | 5 => ⟨((152745815553609/562949953421312), (227036058374729/562949953421312)), (17148605/562949953421312), by norm_num⟩
  | 6 => ⟨((-400946300277329/4503599627370496), (985631001427827/4503599627370496)), (92551453/2251799813685248), by norm_num⟩
  | _ => zero

def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-24205899/16777216), (-18739085/524288)), (1/16777216), by norm_num⟩, -6, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-49810539/33554432), (-1233952337/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((614677331875207/4503599627370496), (814758027299253/4503599627370496)), (62206323/2251799813685248), by norm_num⟩
  | 1 => ⟨((-773510321/2147483648), (-256322997/536870912)), (159/2147483648), by norm_num⟩
  | 2 => ⟨((63791815/134217728), (169112771/268435456)), (107/1073741824), by norm_num⟩
  | 3 => ⟨((-897868037/2147483648), (-595064397/1073741824)), (95/1073741824), by norm_num⟩
  | 4 => ⟨((296190653/1073741824), (785204529/2147483648)), (127/2147483648), by norm_num⟩
  | 5 => ⟨((-625331291/4294967296), (-828879907/4294967296)), (17/536870912), by norm_num⟩
  | 6 => ⟨((275047521/4294967296), (91144233/1073741824)), (61/4294967296), by norm_num⟩
  | 7 => ⟨((-1620237/67108864), (-549793957/17179869184)), (93/17179869184), by norm_num⟩
  | 8 => ⟨((273657493/34359738368), (362734443/34359738368)), (31/17179869184), by norm_num⟩
  | 9 => ⟨((-641953611/274877906944), (-53182055/17179869184)), (147/274877906944), by norm_num⟩
  | 10 => ⟨((677660953/1099511627776), (898243149/1099511627776)), (157/1099511627776), by norm_num⟩
  | 11 => ⟨((-162580555/1099511627776), (-862005515/4398046511104)), (153/4398046511104), by norm_num⟩
  | 12 => ⟨((572079207/17592186044416), (758293991/17592186044416)), (17/2199023255552), by norm_num⟩
  | _ => zero

def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791021039762531/5070602400912917605986812821504), (1204220813611/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889839100022779/316912650057057350374175801344), (1426520752569/633825300114114700748351602688)), (92341/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890764786844375/39614081257132168796771975168), (802312120457/19807040628566084398385987584)), (25973/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((945301793164617/1237940039285380274899124224), (1704654941267/2475880078570760549798248448)), (27599/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((221533700322245/19342813113834066795298816), (1704364397301/154742504910672534362390528)), (13801/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1550564660578643/9671406556917033397649408), (1597532980619/9671406556917033397649408)), (3235/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((1259673266698187/604462909807314587353088), (1397532784939/604462909807314587353088)), (90593/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889229028111941/75557863725914323419136), (567603086753/18889465931478580854784)), (147235/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162327098012975/590295810358705651712), (1702303281331/4722366482869645213696)), (110447/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622928783567839/590295810358705651712), (2339845069785/590295810358705651712)), (75949/295147905179352825856), by norm_num⟩
  | 8 => ⟨((912662231425345/36893488147419103232), (365446737877/9223372036854775808)), (94961/36893488147419103232), by norm_num⟩
  | 7 => ⟨((912368295976649/4611686018427387904), (3287326821699/9223372036854775808)), (213731/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595983372820867/1152921504606846976), (3285210713997/1152921504606846976)), (213817/1152921504606846976), by norm_num⟩
  | 5 => ⟨((37385207704555/4503599627370496), (359022544555/18014398509481984)), (187187/144115188075855872), by norm_num⟩
  | 4 => ⟨((1494252352577961/36028797018963968), (4303516502803/36028797018963968)), (280973/36028797018963968), by norm_num⟩
  | 3 => ⟨((373129899747869/2251799813685248), (671385634615/1125899906842624)), (175777/4503599627370496), by norm_num⟩
  | 2 => ⟨((2234451645157415/4503599627370496), (334914827595/140737488355328)), (704127/4503599627370496), by norm_num⟩
  | 1 => ⟨((556452133856207/562949953421312), (16013798344281/2251799813685248)), (1058741/2251799813685248), by norm_num⟩
  | 0 => ⟨((2199941225540593/2251799813685248), (1986243548231/140737488355328)), (2127711/2251799813685248), by norm_num⟩
  | _ => zero

def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((2199941225540593/2251799813685248), (1986243548231/140737488355328)), (8116573342330168967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2148828419199157/2251799813685248), (62096021703687/2251799813685248)), (4217479/2251799813685248), by norm_num⟩
  | 2 => ⟨((2048853379952985/2251799813685248), (118512929386663/2251799813685248)), (8281845/2251799813685248), by norm_num⟩
  | 3 => ⟨((928980194572873/1125899906842624), (215663590045873/2251799813685248)), (15942619/2251799813685248), by norm_num⟩
  | 4 => ⟨((756174239571891/1125899906842624), (177944062900703/1125899906842624)), (29362289/2251799813685248), by norm_num⟩
  | 5 => ⟨((239868299032561/562949953421312), (478041487107361/2251799813685248)), (48721653/2251799813685248), by norm_num⟩
  | 6 => ⟨((614677331875207/4503599627370496), (814758027299253/4503599627370496)), (62206323/2251799813685248), by norm_num⟩
  | _ => zero

def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-49810539/33554432), (-1233952337/33554432)), (1/16777216), by norm_num⟩, -6, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-1597273/1048576), (-1266211551/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((1962195029511251/9007199254740992), (-72502739030917/9007199254740992)), (124320057/9007199254740992), by norm_num⟩
  | 1 => ⟨((-633445101/1073741824), (11702839/536870912)), (41/1073741824), by norm_num⟩
  | 2 => ⟨((1715401133/2147483648), (-63383751/2147483648)), (113/2147483648), by norm_num⟩
  | 3 => ⟨((-378043/524288), (14303865/536870912)), (13/268435456), by norm_num⟩
  | 4 => ⟨((65520603/134217728), (-1210487/67108864)), (9/268435456), by norm_num⟩
  | 5 => ⟨((-1135571725/4294967296), (20979581/2147483648)), (5/268435456), by norm_num⟩
  | 6 => ⟨((512530873/4294967296), (-37875839/8589934592)), (147/17179869184), by norm_num⟩
  | 7 => ⟨((-793119619/17179869184), (29305621/17179869184)), (29/8589934592), by norm_num⟩
  | 8 => ⟨((4194937/268435456), (-19840273/34359738368)), (81/68719476736), by norm_num⟩
  | 9 => ⟨((-323131733/68719476736), (47758627/274877906944)), (99/274877906944), by norm_num⟩
  | 10 => ⟨((1400091127/1099511627776), (-3233319/68719476736)), (109/1099511627776), by norm_num⟩
  | 11 => ⟨((-1378733475/4398046511104), (50943943/4398046511104)), (109/4398046511104), by norm_num⟩
  | 12 => ⟨((1244559821/17592186044416), (-11496563/4398046511104)), (25/4398046511104), by norm_num⟩
  | _ => zero

def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790995763563793/5070602400912917605986812821504), (-24054685111/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779619402993311/633825300114114700748351602688), (-56986744411/633825300114114700748351602688)), (46103/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((945349356116533/19807040628566084398385987584), (-64101460985/39614081257132168796771975168)), (25933/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1890533473017201/2475880078570760549798248448), (-34048609223/1237940039285380274899124224)), (13777/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((886099795773329/77371252455336267181195264), (-4255332169/9671406556917033397649408)), (13777/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1550499133863585/9671406556917033397649408), (-15954334439/2417851639229258349412352)), (3229/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((629808019698495/302231454903657293676544), (-3489220567/37778931862957161709568)), (90413/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889136237213535/75557863725914323419136), (-45348019519/37778931862957161709568)), (73461/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324636842212931/1180591620717411303424), (-34000651289/2361183241434822606848)), (6887/295147905179352825856), by norm_num⟩
  | 9 => ⟨((405708406627731/147573952589676412928), (-11683515419/73786976294838206464)), (37879/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1825205949537591/73786976294838206464), (-29196168933/18446744073709551616)), (47349/18446744073709551616), by norm_num⟩
  | 7 => ⟨((912301929635529/4611686018427387904), (-32828347451/2305843009213693952)), (106537/4611686018427387904), by norm_num⟩
  | 6 => ⟨((797925691373253/576460752303423488), (-65613366503/576460752303423488)), (106539/576460752303423488), by norm_num⟩
  | 5 => ⟨((74763249340479/9007199254740992), (-114725979697/144115188075855872)), (186447/144115188075855872), by norm_num⟩
  | 4 => ⟨((1494082032326067/36028797018963968), (-171894339043/36028797018963968)), (279679/36028797018963968), by norm_num⟩
  | 3 => ⟨((1492309606290955/9007199254740992), (-214527753915/9007199254740992)), (174807/4503599627370496), by norm_num⟩
  | 2 => ⟨((2234040355338581/4503599627370496), (-428036729839/4503599627370496)), (699273/4503599627370496), by norm_num⟩
  | 1 => ⟨((556303311114305/562949953421312), (-79939275043/281474976710656)), (524515/1125899906842624), by norm_num⟩
  | 0 => ⟨((549709162304939/562949953421312), (-634450522139/1125899906842624)), (1049281/1125899906842624), by norm_num⟩
  | _ => zero

def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((549709162304939/562949953421312), (-634450522139/1125899906842624)), (4002689365867232921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2147118482938961/2251799813685248), (-2478112044805/2251799813685248)), (1025193/562949953421312), by norm_num⟩
  | 2 => ⟨((1023650417484045/1125899906842624), (-295363743141/140737488355328)), (7829299/2251799813685248), by norm_num⟩
  | 3 => ⟨((930681837260617/1125899906842624), (-2148320412061/562949953421312)), (14269413/2251799813685248), by norm_num⟩
  | 4 => ⟨((1538591869171359/2251799813685248), (-7103305634791/1125899906842624)), (23699433/2251799813685248), by norm_num⟩
  | 5 => ⟨((2102374374214523/4503599627370496), (-19413960739329/2251799813685248)), (65370721/4503599627370496), by norm_num⟩
  | 6 => ⟨((1962195029511251/9007199254740992), (-72502739030917/9007199254740992)), (124320057/9007199254740992), by norm_num⟩
  | _ => zero

def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1597273/1048576), (-1266211551/33554432)), (1/16777216), by norm_num⟩, -6, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨38,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 12 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨38,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 12 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨38,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 12 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨38,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 12 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨38,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 12 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨38,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 12 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨38,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiRectangle.Tile038Terms1
