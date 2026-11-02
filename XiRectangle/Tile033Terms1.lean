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
namespace Reinmann.XiRectangle.Tile033Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨33,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5/8), (8319/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((5/8), (8319/640))
  have he : value ((5/8), (8319/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-46079139/33554432), (-958330897/33554432)), (3/67108864), by norm_num⟩
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
  | 0 => ⟨((-1094282362224577/4503599627370496), (80491966788967/1125899906842624)), (73581621/2251799813685248), by norm_num⟩
  | 1 => ⟨((573249841/1073741824), (-168665817/1073741824)), (39/536870912), by norm_num⟩
  | 2 => ⟨((-78722415/134217728), (370596679/2147483648)), (87/1073741824), by norm_num⟩
  | 3 => ⟨((922511067/2147483648), (-67857011/536870912)), (129/2147483648), by norm_num⟩
  | 4 => ⟨((-1013481995/4294967296), (298194185/4294967296)), (9/268435456), by norm_num⟩
  | 5 => ⟨((890739019/8589934592), (-262079837/8589934592)), (129/8589934592), by norm_num⟩
  | 6 => ⟨((-652384555/17179869184), (383898839/34359738368)), (191/34359738368), by norm_num⟩
  | 7 => ⟨((1638211861/137438953472), (-482006837/137438953472)), (121/68719476736), by norm_num⟩
  | 8 => ⟨((-899879841/274877906944), (264769317/274877906944)), (135/274877906944), by norm_num⟩
  | 9 => ⟨((878772491/1099511627776), (-64639739/274877906944)), (67/549755813888), by norm_num⟩
  | 10 => ⟨((-386172103/2199023255552), (227244837/4398046511104)), (239/8796093022208), by norm_num⟩
  | 11 => ⟨((1234191761/35184372088832), (-45391631/4398046511104)), (193/35184372088832), by norm_num⟩
  | 12 => ⟨((-903932157/140737488355328), (265961619/140737488355328)), (143/140737488355328), by norm_num⟩
  | _ => zero

def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791093467826773/5070602400912917605986812821504), (1859764829133/5070602400912917605986812821504)), (7279/1267650600228229401496703205376), by norm_num⟩
  | 17 => ⟨((1779840527642339/633825300114114700748351602688), (4406965099621/633825300114114700748351602688)), (17369/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1890946837672093/39614081257132168796771975168), (2478601680119/19807040628566084398385987584)), (78181/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472699075233741/618970019642690137449562112), (82285736705/38685626227668133590597632)), (83091/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221557689224909/19342813113834066795298816), (5265452869131/154742504910672534362390528)), (41559/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1550743724103589/9671406556917033397649408), (4935475563169/9671406556917033397649408)), (609/75557863725914323419136), by norm_num⟩
  | 12 => ⟨((78739318401995/37778931862957161709568), (2158827263517/302231454903657293676544)), (68237/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472370162480627/18889465931478580854784), (219203939371/2361183241434822606848)), (110939/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324701025706275/1180591620717411303424), (328714976763/295147905179352825856)), (20813/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1623184077221243/590295810358705651712), (7229364896779/590295810358705651712)), (114549/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825640178283993/73786976294838206464), (4516579309139/36893488147419103232)), (143301/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1825087099036433/9223372036854775808), (158709759909/144115188075855872)), (161373/9223372036854775808), by norm_num⟩
  | 6 => ⟨((798164022814333/576460752303423488), (5075662316813/576460752303423488)), (40393/288230376151711744), by norm_num⟩
  | 5 => ⟨((598310840450901/72057594037927936), (8875544520591/144115188075855872)), (4425/4503599627370496), by norm_num⟩
  | 4 => ⟨((747340909213561/18014398509481984), (13299582661593/36028797018963968)), (212847/36028797018963968), by norm_num⟩
  | 3 => ⟨((1493033583125859/9007199254740992), (16600432338313/9007199254740992)), (266845/9007199254740992), by norm_num⟩
  | 2 => ⟨((1117705637950237/2251799813685248), (16564341010865/2251799813685248)), (134013/1125899906842624), by norm_num⟩
  | 1 => ⟨((1113538930939175/1125899906842624), (1547262872503/70368744177664)), (404995/1125899906842624), by norm_num⟩
  | 0 => ⟨((1100901870879227/1125899906842624), (49150733998359/1125899906842624)), (410925/562949953421312), by norm_num⟩
  | _ => zero

def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((1100901870879227/1125899906842624), (49150733998359/1125899906842624)), (1567554476024436773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((134289150316747/140737488355328), (48059454206389/562949953421312)), (1678961/1125899906842624), by norm_num⟩
  | 2 => ⟨((1016884365676013/1125899906842624), (45857456641319/281474976710656)), (3490737/1125899906842624), by norm_num⟩
  | 3 => ⟨((888540185324285/1125899906842624), (165669187553245/562949953421312)), (3721451/562949953421312), by norm_num⟩
  | 4 => ⟨((301855670289577/562949953421312), (261486353656231/562949953421312)), (16128321/1125899906842624), by norm_num⟩
  | 5 => ⟨((80794864265735/1125899906842624), (280419735625795/562949953421312)), (64558217/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1094282362224577/4503599627370496), (80491966788967/1125899906842624)), (73581621/2251799813685248), by norm_num⟩
  | _ => zero

def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-46079139/33554432), (-958330897/33554432)), (3/67108864), by norm_num⟩, -5, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-96577419/67108864), (-2008568865/67108864)), (3/67108864), by norm_num⟩
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
  | 0 => ⟨((45269368364411/2251799813685248), (1064127076533877/4503599627370496)), (15527429/562949953421312), by norm_num⟩
  | 1 => ⟨((-49703871/1073741824), (-584183489/1073741824)), (139/2147483648), by norm_num⟩
  | 2 => ⟨((3576481/67108864), (672566097/1073741824)), (163/2147483648), by norm_num⟩
  | 3 => ⟨((-21960405/536870912), (-1032427113/2147483648)), (127/2147483648), by norm_num⟩
  | 4 => ⟨((50565701/2147483648), (148578205/536870912)), (37/1073741824), by norm_num⟩
  | 5 => ⟨((-93145463/8589934592), (-8552849/67108864)), (69/4294967296), by norm_num⟩
  | 6 => ⟨((71491785/17179869184), (420131469/8589934592)), (107/17179869184), by norm_num⟩
  | 7 => ⟨((-94066239/68719476736), (-1105586809/68719476736)), (143/68719476736), by norm_num⟩
  | 8 => ⟨((3384305/8589934592), (1272853853/274877906944)), (167/274877906944), by norm_num⟩
  | 9 => ⟨((-110828803/1099511627776), (-1302601915/1099511627776)), (173/1099511627776), by norm_num⟩
  | 10 => ⟨((25519275/1099511627776), (1199740701/4398046511104)), (161/4398046511104), by norm_num⟩
  | 11 => ⟨((-42734765/8796093022208), (-251136823/4398046511104)), (137/17592186044416), by norm_num⟩
  | 12 => ⟨((131200577/140737488355328), (192754635/17592186044416)), (53/35184372088832), by norm_num⟩
  | _ => zero

def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791050579121697/5070602400912917605986812821504), (1935574241359/10141204801825835211973625643008)), (7279/1267650600228229401496703205376), by norm_num⟩
  | 17 => ⟨((1779746465823659/633825300114114700748351602688), (2293053952129/633825300114114700748351602688)), (8665/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((945420737591113/19807040628566084398385987584), (40302391573/618970019642690137449562112)), (19499/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1890684928319063/2475880078570760549798248448), (1370079884219/1237940039285380274899124224)), (41441/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((886175393925101/77371252455336267181195264), (1369853304495/77371252455336267181195264)), (82897/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550640605327915/9671406556917033397649408), (2567993532665/9671406556917033397649408)), (77731/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629869775993969/302231454903657293676544), (2246513005021/604462909807314587353088)), (68029/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472334107484157/18889465931478580854784), (3649681292101/75557863725914323419136)), (6911/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((324674265709331/1180591620717411303424), (342058948089/590295810358705651712)), (20739/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1623038724103397/590295810358705651712), (3761365987017/590295810358705651712)), (114105/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912730612487883/36893488147419103232), (4699784359197/73786976294838206464)), (142691/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1824889537847827/9223372036854775808), (5284613982699/9223372036854775808)), (160611/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1596135180660337/1152921504606846976), (2640655509179/576460752303423488)), (80357/576460752303423488), by norm_num⟩
  | 5 => ⟨((598229099950179/72057594037927936), (2308716555425/72057594037927936)), (140741/144115188075855872), by norm_num⟩
  | 4 => ⟨((747223565056729/18014398509481984), (3459363058925/18014398509481984)), (13209/2251799813685248), by norm_num⟩
  | 3 => ⟨((746379307093183/4503599627370496), (1079428323809/1125899906842624)), (264589/9007199254740992), by norm_num⟩
  | 2 => ⟨((279364543236893/562949953421312), (2153993828305/562949953421312)), (132601/1125899906842624), by norm_num⟩
  | 1 => ⟨((556618100994159/562949953421312), (12875405864445/1125899906842624)), (199669/562949953421312), by norm_num⟩
  | 0 => ⟨((1100568539941043/1125899906842624), (25557009909583/1125899906842624)), (25151/35184372088832), by norm_num⟩
  | _ => zero

def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((1100568539941043/1125899906842624), (25557009909583/1125899906842624)), (95943451061952103/134217728000000000000000000), by norm_num⟩
  | 1 => ⟨((2150453948872483/2251799813685248), (49964017068491/1125899906842624)), (1609987/1125899906842624), by norm_num⟩
  | 2 => ⟨((512308703705641/562949953421312), (95430612573527/1125899906842624)), (3217947/1125899906842624), by norm_num⟩
  | 3 => ⟨((924357328239419/1125899906842624), (347383870443557/2251799813685248)), (1600611/281474976710656), by norm_num⟩
  | 4 => ⟨((1464193356619657/2251799813685248), (142600076794197/562949953421312)), (24976285/2251799813685248), by norm_num⟩
  | 5 => ⟨((807578748381561/2251799813685248), (185446400542869/562949953421312)), (45134201/2251799813685248), by norm_num⟩
  | 6 => ⟨((45269368364411/2251799813685248), (1064127076533877/4503599627370496)), (15527429/562949953421312), by norm_num⟩
  | _ => zero

def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-96577419/67108864), (-2008568865/67108864)), (3/67108864), by norm_num⟩, -5, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-50287509/33554432), (-522927231/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((975664867599187/4503599627370496), (246048682485749/4503599627370496)), (38562053/2251799813685248), by norm_num⟩
  | 1 => ⟨((-557790321/1073741824), (-281333433/2147483648)), (91/2147483648), by norm_num⟩
  | 2 => ⟨((668761387/1073741824), (337304055/2147483648)), (111/2147483648), by norm_num⟩
  | 3 => ⟨((-534539923/1073741824), (-33700825/268435456)), (91/2147483648), by norm_num⟩
  | 4 => ⟨((640885377/2147483648), (80811049/1073741824)), (7/268435456), by norm_num⟩
  | 5 => ⟨((-1229420813/8589934592), (-77510573/2147483648)), (55/4294967296), by norm_num⟩
  | 6 => ⟨((982674119/17179869184), (247816315/17179869184)), (45/8589934592), by norm_num⟩
  | 7 => ⟨((-336621375/17179869184), (-169782163/34359738368)), (125/68719476736), by norm_num⟩
  | 8 => ⟨((201795701/34359738368), (203559923/137438953472)), (19/34359738368), by norm_num⟩
  | 9 => ⟨((-215059981/137438953472), (-27117521/68719476736)), (83/549755813888), by norm_num⟩
  | 10 => ⟨((825106099/2199023255552), (416159843/4398046511104)), (81/2199023255552), by norm_num⟩
  | 11 => ⟨((-89932637/1099511627776), (-362875535/17592186044416)), (9/1099511627776), by norm_num⟩
  | 12 => ⟨((1150128241/70368744177664), (290045843/70368744177664)), (117/70368744177664), by norm_num⟩
  | _ => zero

def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791011781571557/5070602400912917605986812821504), (160895131841/5070602400912917605986812821504)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889828637662037/316912650057057350374175801344), (190592009981/316912650057057350374175801344)), (46119/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((945370654247593/19807040628566084398385987584), (428775201673/39614081257132168796771975168)), (51885/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((945289359481223/1237940039285380274899124224), (455503996001/2475880078570760549798248448)), (110259/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886122411670637/77371252455336267181195264), (455425652949/154742504910672534362390528)), (55131/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1550541523640991/9671406556917033397649408), (426878329059/9671406556917033397649408)), (51687/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314913278856949/151115727451828646838272), (373435338623/604462909807314587353088)), (90455/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((236149557200593/9444732965739290427392), (303338235885/37778931862957161709568)), (36749/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1298592509518073/4722366482869645213696), (113717734927/1180591620717411303424)), (110253/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622895654930555/590295810358705651712), (625225953845/590295810358705651712)), (75803/295147905179352825856), by norm_num⟩
  | 8 => ⟨((228160428138295/9223372036854775808), (781200208071/73786976294838206464)), (189521/73786976294838206464), by norm_num⟩
  | 7 => ⟨((912345468455139/4611686018427387904), (219598413155/2305843009213693952)), (213229/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595938357511401/1152921504606846976), (109727910813/144115188075855872)), (53313/288230376151711744), by norm_num⟩
  | 5 => ⟨((598143988382079/72057594037927936), (23982944045/4503599627370496)), (93311/72057594037927936), by norm_num⟩
  | 4 => ⟨((373548945605481/9007199254740992), (1149900219695/36028797018963968)), (279985/36028797018963968), by norm_num⟩
  | 3 => ⟨((1492451390606801/9007199254740992), (1435136142047/9007199254740992)), (350073/9007199254740992), by norm_num⟩
  | 2 => ⟨((139645169811853/281474976710656), (2863566003153/4503599627370496)), (700421/4503599627370496), by norm_num⟩
  | 1 => ⟨((2225633779719411/2251799813685248), (2139311073627/1125899906842624)), (1051325/2251799813685248), by norm_num⟩
  | 0 => ⟨((2199665752130679/2251799813685248), (265330294505/70368744177664)), (1052723/1125899906842624), by norm_num⟩
  | _ => zero

def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((2199665752130679/2251799813685248), (265330294505/70368744177664)), (4015819553855514171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2148706693162463/2251799813685248), (16587988563555/2251799813685248)), (4129279/2251799813685248), by norm_num⟩
  | 2 => ⟨((64069101300365/70368744177664), (31657096546501/2251799813685248)), (3970649/1125899906842624), by norm_num⟩
  | 3 => ⟨((1866224492039393/2251799813685248), (28823048488579/1125899906842624)), (14684021/2251799813685248), by norm_num⟩
  | 4 => ⟨((193149428794947/281474976710656), (95550730038641/2251799813685248)), (6272795/562949953421312), by norm_num⟩
  | 5 => ⟨((528132865439001/1125899906842624), (65567352180209/1125899906842624)), (36564759/2251799813685248), by norm_num⟩
  | 6 => ⟨((975664867599187/4503599627370496), (246048682485749/4503599627370496)), (38562053/2251799813685248), by norm_num⟩
  | _ => zero

def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-50287509/33554432), (-522927231/16777216)), (1/16777216), by norm_num⟩, -5, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-52112269/33554432), (-1083804925/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((604249130331543/4503599627370496), (-46055439382475/281474976710656)), (14218917/562949953421312), by norm_num⟩
  | 1 => ⟨((-44748267/134217728), (873134365/2147483648)), (137/2147483648), by norm_num⟩
  | 2 => ⟨((444781065/1073741824), (-1084828695/2147483648)), (173/2147483648), by norm_num⟩
  | 3 => ⟨((-184206571/536870912), (224641503/536870912)), (73/1073741824), by norm_num⟩
  | 4 => ⟨((457736133/2147483648), (-1116426329/4294967296)), (23/536870912), by norm_num⟩
  | 5 => ⟨((-28435789/268435456), (1109686083/8589934592)), (93/4294967296), by norm_num⟩
  | 6 => ⟨((376854833/8589934592), (-459577721/8589934592)), (39/4294967296), by norm_num⟩
  | 7 => ⟨((-16722305/1073741824), (81571981/4294967296)), (113/34359738368), by norm_num⟩
  | 8 => ⟨((332426935/68719476736), (-101349379/17179869184)), (71/68719476736), by norm_num⟩
  | 9 => ⟨((-734266579/549755813888), (895444429/549755813888)), (159/549755813888), by norm_num⟩
  | 10 => ⟨((364916781/1099511627776), (-445019163/1099511627776)), (5/68719476736), by norm_num⟩
  | 11 => ⟨((-659479371/8796093022208), (804240783/8796093022208)), (147/8796093022208), by norm_num⟩
  | 12 => ⟨((546248225/35184372088832), (-666154423/35184372088832)), (31/8796093022208), by norm_num⟩
  | _ => zero

def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197744090550571/1267650600228229401496703205376), (-143934882163/1267650600228229401496703205376)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889786224521513/316912650057057350374175801344), (-1363888560799/633825300114114700748351602688)), (92335/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945322919279551/19807040628566084398385987584), (-1534163417729/39614081257132168796771975168)), (103885/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((59077413445723/77371252455336267181195264), (-814895136883/1237940039285380274899124224)), (27597/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((886071638151291/77371252455336267181195264), (-1629499687069/154742504910672534362390528)), (110399/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550446261340765/9671406556917033397649408), (-1527347273757/9671406556917033397649408)), (103511/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314892424750515/151115727451828646838272), (-83507515959/37778931862957161709568)), (11323/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((472265197476893/18889465931478580854784), (-542654232305/18889465931478580854784)), (147221/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298490657322063/4722366482869645213696), (-813728339199/2361183241434822606848)), (110435/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202844430437659/73786976294838206464), (-2236930946021/590295810358705651712)), (18985/73786976294838206464), by norm_num⟩
  | 8 => ⟨((228138489262169/9223372036854775808), (-2794931215483/73786976294838206464)), (94949/36893488147419103232), by norm_num⟩
  | 7 => ⟨((912246574107889/4611686018427387904), (-785650952179/2305843009213693952)), (213701/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595740145955505/1152921504606846976), (-3140487797473/1152921504606846976)), (213783/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196114066826889/144115188075855872), (-1372774013715/72057594037927936)), (187153/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493933970094425/36028797018963968), (-4113568740773/36028797018963968)), (280913/36028797018963968), by norm_num⟩
  | 3 => ⟨((1492122472219431/9007199254740992), (-5133652295699/9007199254740992)), (175733/4503599627370496), by norm_num⟩
  | 2 => ⟨((2233659941280265/4503599627370496), (-10242417242649/4503599627370496)), (703907/4503599627370496), by norm_num⟩
  | 1 => ⟨((2224627338637467/2251799813685248), (-15301542211767/2251799813685248)), (1058301/2251799813685248), by norm_num⟩
  | 0 => ⟨((549401044344679/562949953421312), (-15177778356955/1125899906842624)), (531599/562949953421312), by norm_num⟩
  | _ => zero

def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((549401044344679/562949953421312), (-15177778356955/1125899906842624)), (2027889253856468023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2144303694877157/2251799813685248), (-59249936726809/2251799813685248)), (525971/281474976710656), by norm_num⟩
  | 2 => ⟨((2040380211837033/2251799813685248), (-112842942318755/2251799813685248)), (8235229/2251799813685248), by norm_num⟩
  | 3 => ⟨((1843155796532595/2251799813685248), (-204496425617733/2251799813685248)), (15749435/2251799813685248), by norm_num⟩
  | 4 => ⟨((1490098934109907/2251799813685248), (-334771119490115/2251799813685248)), (3580399/281474976710656), by norm_num⟩
  | 5 => ⟨((468141776675161/1125899906842624), (-443060777686633/2251799813685248)), (46425179/2251799813685248), by norm_num⟩
  | 6 => ⟨((604249130331543/4503599627370496), (-46055439382475/281474976710656)), (14218917/562949953421312), by norm_num⟩
  | _ => zero

def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-52112269/33554432), (-1083804925/33554432)), (1/16777216), by norm_num⟩, -5, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-53790887/33554432), (-1118715967/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-313893425977361/4503599627370496), (-850369052145759/4503599627370496)), (78614097/2251799813685248), by norm_num⟩
  | 1 => ⟨((191955743/1073741824), (520027531/1073741824)), (195/2147483648), by norm_num⟩
  | 2 => ⟨((-61544595/268435456), (-666922141/1073741824)), (63/536870912), by norm_num⟩
  | 3 => ⟨((210478359/1073741824), (1140414345/2147483648)), (109/1073741824), by norm_num⟩
  | 4 => ⟨((-134966583/1073741824), (-1462552521/4294967296)), (141/2147483648), by norm_num⟩
  | 5 => ⟨((553891921/8589934592), (375137315/2147483648)), (73/2147483648), by norm_num⟩
  | 6 => ⟨((-236784121/8589934592), (-1282944287/17179869184)), (63/4294967296), by norm_num⟩
  | 7 => ⟨((347051017/34359738368), (940196321/34359738368)), (187/34359738368), by norm_num⟩
  | 8 => ⟨((-222542071/68719476736), (-1205777975/137438953472)), (121/68719476736), by norm_num⟩
  | 9 => ⟨((31711619/34359738368), (171819969/68719476736)), (139/274877906944), by norm_num⟩
  | 10 => ⟨((-520567659/2199023255552), (-1410270461/2199023255552)), (9/68719476736), by norm_num⟩
  | 11 => ⟨((242769033/4398046511104), (657685875/4398046511104)), (271/8796093022208), by norm_num⟩
  | 12 => ⟨((-207563425/17592186044416), (-562310321/17592186044416)), (117/17592186044416), by norm_num⟩
  | _ => zero

def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581887559023027/10141204801825835211973625643008), (-156672216525/633825300114114700748351602688)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889745774536651/316912650057057350374175801344), (-2968923358057/633825300114114700748351602688)), (23123/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((945277311738183/19807040628566084398385987584), (-3339557808337/39614081257132168796771975168)), (104073/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945190027691147/1237940039285380274899124224), (-1773849430347/1237940039285380274899124224)), (55299/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((886022905189787/77371252455336267181195264), (-3547044945005/154742504910672534362390528)), (110623/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550354577963715/9671406556917033397649408), (-3324659939867/9671406556917033397649408)), (103735/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259489167150707/604462909807314587353088), (-1454191425869/302231454903657293676544)), (45397/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((472232336711497/18889465931478580854784), (-590602497589/9444732965739290427392)), (147589/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324597892237665/1180591620717411303424), (-3542475814879/4722366482869645213696)), (110735/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811309187662957/295147905179352825856), (-4869053493663/590295810358705651712)), (152329/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912467673809347/36893488147419103232), (-6083541440571/73786976294838206464)), (190515/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1824297319955361/9223372036854775808), (-3420084524567/4611686018427387904)), (26809/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1595542206992819/1152921504606846976), (-6835401920557/1152921504606846976)), (214651/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597969249916719/72057594037927936), (-93369000229/2251799813685248)), (188021/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493665889139161/36028797018963968), (-8952708579227/36028797018963968)), (141217/18014398509481984), by norm_num⟩
  | 3 => ⟨((186472389492715/1125899906842624), (-5586073480597/4503599627370496)), (353749/9007199254740992), by norm_num⟩
  | 2 => ⟨((279118569531739/562949953421312), (-5572032685331/1125899906842624)), (44351/281474976710656), by norm_num⟩
  | 1 => ⟨((1111749452007817/1125899906842624), (-16645987150981/1125899906842624)), (534867/1125899906842624), by norm_num⟩
  | 0 => ⟨((1097551909649887/1125899906842624), (-16506045084809/562949953421312)), (540191/562949953421312), by norm_num⟩
  | _ => zero

def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((1097551909649887/1125899906842624), (-16506045084809/562949953421312)), (2060665132762718023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1068949725427923/1125899906842624), (-16090454571937/281474976710656)), (542429/281474976710656), by norm_num⟩
  | 2 => ⟨((1011200964597171/1125899906842624), (-61106273806937/562949953421312)), (4367999/1125899906842624), by norm_num⟩
  | 3 => ⟨((223730252992377/281474976710656), (-439049493767481/2251799813685248)), (17588595/2251799813685248), by norm_num⟩
  | 4 => ⟨((1337050475971605/2251799813685248), (-697956567682735/2251799813685248)), (17409661/1125899906842624), by norm_num⟩
  | 5 => ⟨((288782465701505/1125899906842624), (-51803181801297/140737488355328)), (31467081/1125899906842624), by norm_num⟩
  | 6 => ⟨((-313893425977361/4503599627370496), (-850369052145759/4503599627370496)), (78614097/2251799813685248), by norm_num⟩
  | _ => zero

def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-53790887/33554432), (-1118715967/33554432)), (1/16777216), by norm_num⟩, -5, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-13836261/8388608), (-1151038543/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-418840391200825/2251799813685248), (-217376186190995/4503599627370496)), (297041395/9007199254740992), by norm_num⟩
  | 1 => ⟨((1054137997/2147483648), (136773161/1073741824)), (189/2147483648), by norm_num⟩
  | 2 => ⟨((-1390965303/2147483648), (-360952213/2147483648)), (63/536870912), by norm_num⟩
  | 3 => ⟨((152951549/268435456), (19845283/134217728)), (7/67108864), by norm_num⟩
  | 4 => ⟨((-1614591625/4294967296), (-104745679/1073741824)), (149/2147483648), by norm_num⟩
  | 5 => ⟨((213049993/1073741824), (442287763/8589934592)), (317/8589934592), by norm_num⟩
  | 6 => ⟨((-374834097/4294967296), (-194537127/8589934592)), (281/17179869184), by norm_num⟩
  | 7 => ⟨((1130524195/34359738368), (36671045/4294967296)), (107/17179869184), by norm_num⟩
  | 8 => ⟨((-1491759081/137438953472), (-48388495/17179869184)), (285/137438953472), by norm_num⟩
  | 9 => ⟨((437426415/137438953472), (56755561/68719476736)), (169/274877906944), by norm_num⟩
  | 10 => ⟨((-923514709/1099511627776), (-239649887/1099511627776)), (45/274877906944), by norm_num⟩
  | 11 => ⟨((443128775/2199023255552), (114990871/2199023255552)), (175/4398046511104), by norm_num⟩
  | 12 => ⟨((-779628161/17592186044416), (-202311667/17592186044416)), (311/35184372088832), by norm_num⟩
  | _ => zero

def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581827225323591/10141204801825835211973625643008), (-3761545415079/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889707098891701/316912650057057350374175801344), (-4454717340959/633825300114114700748351602688)), (46319/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890467275388249/39614081257132168796771975168), (-2505399504125/19807040628566084398385987584)), (52123/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1890286828176523/2475880078570760549798248448), (-2661537312901/1237940039285380274899124224)), (55397/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((442988027769527/38685626227668133590597632), (-166314461349/4835703278458516698824704)), (110831/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((96891639595785/604462909807314587353088), (-311772420869/604462909807314587353088)), (103943/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629705682367973/302231454903657293676544), (-1090934695641/151115727451828646838272)), (90989/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888801979110969/75557863725914323419136), (-7089059685157/75557863725914323419136)), (73965/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298295222323913/4722366482869645213696), (-5315030901419/4722366482869645213696)), (27753/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1622484566061563/590295810358705651712), (-913162650465/73786976294838206464)), (152745/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824766089139387/73786976294838206464), (-2281831765499/18446744073709551616)), (191087/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1824104161809297/9223372036854775808), (-5131165596125/4611686018427387904)), (53797/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1595345625967797/1152921504606846976), (-10254941480343/1152921504606846976)), (6733/36028797018963968), by norm_num⟩
  | 5 => ⟨((1195762647662443/144115188075855872), (-8964760351473/144115188075855872)), (188827/144115188075855872), by norm_num⟩
  | 4 => ⟨((373348610184661/9007199254740992), (-13430513628693/36028797018963968)), (283845/36028797018963968), by norm_num⟩
  | 3 => ⟨((372856605456837/2251799813685248), (-8379522516143/4503599627370496)), (355867/9007199254740992), by norm_num⟩
  | 2 => ⟨((139512698351951/281474976710656), (-8357699948641/1125899906842624)), (89365/562949953421312), by norm_num⟩
  | 1 => ⟨((555570347795395/562949953421312), (-1560249334345/70368744177664)), (135045/281474976710656), by norm_num⟩
  | 0 => ⟨((68508572395781/70368744177664), (-49491559094623/1125899906842624)), (1096375/1125899906842624), by norm_num⟩
  | _ => zero

def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((68508572395781/70368744177664), (-49491559094623/1125899906842624)), (4182338718894576671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1064985660064741/1125899906842624), (-96366535990855/1125899906842624)), (1115587/562949953421312), by norm_num⟩
  | 2 => ⟨((499559481286063/562949953421312), (-45576422165349/281474976710656)), (1150715/281474976710656), by norm_num⟩
  | 3 => ⟨((26784223096457/35184372088832), (-20222165112035/70368744177664)), (9659709/1125899906842624), by norm_num⟩
  | 4 => ⟨((1118970642757957/2251799813685248), (-985228292582423/2251799813685248)), (40517753/2251799813685248), by norm_num⟩
  | 5 => ⟨((249951624597315/4503599627370496), (-979164781091305/2251799813685248)), (151447591/4503599627370496), by norm_num⟩
  | 6 => ⟨((-418840391200825/2251799813685248), (-217376186190995/4503599627370496)), (297041395/9007199254740992), by norm_num⟩
  | _ => zero

def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-13836261/8388608), (-1151038543/33554432)), (1/16777216), by norm_num⟩, -5, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-56791929/33554432), (-590565071/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-331709356215223/2251799813685248), (496943369170897/4503599627370496)), (149560089/4503599627370496), by norm_num⟩
  | 1 => ⟨((856671895/2147483648), (-641702457/2147483648)), (195/2147483648), by norm_num⟩
  | 2 => ⟨((-1159955249/2147483648), (434440617/1073741824)), (267/2147483648), by norm_num⟩
  | 3 => ⟨((261768087/536870912), (-784324667/2147483648)), (243/2147483648), by norm_num⟩
  | 4 => ⟨((-708881121/2147483648), (530997643/2147483648)), (83/1073741824), by norm_num⟩
  | 5 => ⟨((767874265/4294967296), (-575187309/4294967296)), (91/2147483648), by norm_num⟩
  | 6 => ⟨((-86643419/1073741824), (129803009/2147483648)), (83/4294967296), by norm_num⟩
  | 7 => ⟨((268153975/8589934592), (-803458433/34359738368)), (259/34359738368), by norm_num⟩
  | 8 => ⟨((-363087213/34359738368), (543951443/68719476736)), (177/68719476736), by norm_num⟩
  | 9 => ⟨((874007467/274877906944), (-327343959/137438953472)), (215/274877906944), by norm_num⟩
  | 10 => ⟨((-946742439/1099511627776), (709171099/1099511627776)), (235/1099511627776), by norm_num⟩
  | 11 => ⟨((932300383/4398046511104), (-174588267/1099511627776)), (117/2199023255552), by norm_num⟩
  | 12 => ⟨((-52598255/1099511627776), (315195861/8796093022208)), (213/17592186044416), by norm_num⟩
  | _ => zero

def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581771056014629/10141204801825835211973625643008), (3254823446855/10141204801825835211973625643008)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889675172736861/316912650057057350374175801344), (481792911347/79228162514264337593543950336)), (92579/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890395607260965/39614081257132168796771975168), (4335471026251/39614081257132168796771975168)), (6511/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((1890210890679729/2475880078570760549798248448), (287852524139/154742504910672534362390528)), (110715/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771876409610799/154742504910672534362390528), (2302371550681/77371252455336267181195264)), (110747/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550195514073747/9671406556917033397649408), (2157996680957/4835703278458516698824704)), (103859/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259349735747611/604462909807314587353088), (3775540974127/604462909807314587353088)), (45455/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((472175575372625/18889465931478580854784), (766683370773/9444732965739290427392)), (9237/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((324555218658757/1180591620717411303424), (4598536663857/4722366482869645213696)), (27725/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1622383004582201/590295810358705651712), (6320447439095/590295810358705651712)), (152577/590295810358705651712), by norm_num⟩
  | 8 => ⟨((114040008517645/4611686018427387904), (7896749136419/73786976294838206464)), (23857/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1823963837001411/9223372036854775808), (1109825587239/1152921504606846976)), (214899/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595207014168481/1152921504606846976), (8872058440137/1152921504606846976)), (215131/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195643286465787/144115188075855872), (3877844223833/72057594037927936)), (188501/144115188075855872), by norm_num⟩
  | 4 => ⟨((373304809920473/9007199254740992), (11618811945989/36028797018963968)), (283275/36028797018963968), by norm_num⟩
  | 3 => ⟨((1491214124884487/9007199254740992), (1812220521685/1125899906842624)), (355011/9007199254740992), by norm_num⟩
  | 2 => ⟨((1115899312612449/2251799813685248), (14459159179679/2251799813685248)), (356389/2251799813685248), by norm_num⟩
  | 1 => ⟨((1110862222741541/1125899906842624), (10796150422627/562949953421312)), (269017/562949953421312), by norm_num⟩
  | 0 => ⟨((547839628061213/562949953421312), (42799301767951/1125899906842624)), (272479/281474976710656), by norm_num⟩
  | _ => zero

def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((547839628061213/562949953421312), (42799301767951/1125899906842624)), (1039424897313976199/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1064642820183409/1125899906842624), (83301023188063/1125899906842624)), (1102093/562949953421312), by norm_num⟩
  | 2 => ⟨((7816839357077/8796093022208), (157537691782577/1125899906842624)), (1123671/281474976710656), by norm_num⟩
  | 3 => ⟨((867122426831357/1125899906842624), (279998591702023/1125899906842624)), (9246405/1125899906842624), by norm_num⟩
  | 4 => ⟨((598190023523047/1125899906842624), (862574219503715/2251799813685248)), (37682731/2251799813685248), by norm_num⟩
  | 5 => ⟨((76304621823017/562949953421312), (916570450924505/2251799813685248)), (34455559/1125899906842624), by norm_num⟩
  | 6 => ⟨((-331709356215223/2251799813685248), (496943369170897/4503599627370496)), (149560089/4503599627370496), by norm_num⟩
  | _ => zero

def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-56791929/33554432), (-590565071/16777216)), (1/16777216), by norm_num⟩, -6, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨33,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 12 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨33,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 12 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨33,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 12 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨33,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 12 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨33,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 12 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨33,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 12 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨33,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiRectangle.Tile033Terms1
