/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ZetaBoxNumeric
import RHV6Fresh.Terminal.ZetaBox22.Base
/-!
# Certificat (V2), côté b1left (b1), angles 8

Fichier GENERE par `experiments/e192_zeta_box_certificate_generator.py` : constantes rationnelles calculees en
arithmetique exacte puis verifiees par Lean (`norm_num`, `linarith`, `decide`). Aucune preuve admise, aucun axiome ajoute.
-/

set_option maxHeartbeats 4000000
set_option linter.style.longLine false

namespace RHV6Fresh
namespace ZB
namespace Cert
namespace H22

open Complex Set

lemma cs_b1left_v21p171_34 : ‖exp (-((((((21171:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7373583564582:ℝ):ℂ) + ((0.6755017795396:ℝ):ℂ) * I)‖ ≤ 0.00000014704 := by
  have hl := lg_34
  refine (ecis_approx ((((21171:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.656578639132224214 74.656578692059745385 0.741645 0.00000004703 0.7373583564582 0.6755017795396 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p171_35 : ‖exp (-((((((21171:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9918255727624:ℝ):ℂ) + ((0.1276010705851:ℝ):ℂ) * I)‖ ≤ 0.00000014398 := by
  have hl := lg_35
  refine (ecis_approx ((((21171:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.270273787779137901 75.270273830121201414 0.1279499 0.00000004397 0.9918255727624 0.1276010705851 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p171_36 : ‖exp (-((((((21171:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8922665719233:ℝ):ℂ) + (((-0.4515089862099):ℝ):ℂ) * I)‖ ≤ 0.00000016213 := by
  have hl := lg_36
  refine (ecis_approx ((((21171:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.866679424041080088 75.86667946638312243 (-0.4684558) 0.00000006212 0.8922665719233 (-0.4515089862099) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p171_37 : ‖exp (-((((((21171:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4988548088687:ℝ):ℂ) + (((-0.8666855713975):ℝ):ℂ) * I)‖ ≤ 0.00000016278 := by
  have hl := lg_37
  refine (ecis_approx ((((21171:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.446743106577641582 76.446743148919705095 (-1.0485194) 0.00000006277 0.4988548088687 (-0.8666855713975) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p171_38 : ‖exp (-((((((21171:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0423039450084):ℝ):ℂ) + (((-0.9991047874154):ℝ):ℂ) * I)‖ ≤ 0.00000012176 := by
  have hl := lg_38
  refine (ecis_approx ((((21171:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.011336565554072113 77.011336607896135626 (-1.6131129) 0.00000002175 (-0.0423039450084) (-0.9991047874154) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p171_39 : ‖exp (-((((((21171:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5582238973363):ℝ):ℂ) + (((-0.8296903521396):ℝ):ℂ) * I)‖ ≤ 0.0000001444 := by
  have hl := lg_39
  refine (ecis_approx ((((21171:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.561263588197510744 77.561263630539574257 (-2.1630399) 0.00000004439 (-0.5582238973363) (-0.8296903521396) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p171_40 : ‖exp (-((((((21171:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9036628111503):ℝ):ℂ) + (((-0.4282447006364):ℝ):ℂ) * I)‖ ≤ 0.00000016232 := by
  have hl := lg_40
  refine (ecis_approx ((((21171:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 78.097266895529618739 78.09726694845713991 (-2.6990432) 0.00000006231 (-0.9036628111503) (-0.4282447006364) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p171_41 : ‖exp (-((((((21171:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9967842727078):ℝ):ℂ) + ((0.0801318486626:ℝ):ℂ) * I)‖ ≤ 0.00000015629 := by
  have hl := lg_41
  refine (ecis_approx ((((21171:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 78.62003419668036318 78.620034249607905522 3.0613748 0.00000005628 (-0.9967842727078) 0.0801318486626 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p171_42 : ‖exp (-((((((21171:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8307252196499):ℝ):ℂ) + ((0.5566826828407:ℝ):ℂ) * I)‖ ≤ 0.00000012669 := by
  have hl := lg_42
  refine (ecis_approx ((((21171:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.130203466663959206 79.130203509006022719 2.5512055 0.00000002668 (-0.8307252196499) 0.5566826828407 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p171_43 : ‖exp (-((((((21171:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4637692900425):ℝ):ℂ) + ((0.8859560065875:ℝ):ℂ) * I)‖ ≤ 0.00000016601 := by
  have hl := lg_43
  refine (ecis_approx ((((21171:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.62836762733517638 79.628367669677261064 2.0530413 0.000000066 (-0.4637692900425) 0.8859560065875 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p171_44 : ‖exp (-((((((21171:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0044660119488:ℝ):ℂ) + ((0.9999900273188:ℝ):ℂ) * I)‖ ≤ 0.00000017177 := by
  have hl := lg_44
  refine (ecis_approx ((((21171:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.115078712166962143 80.115078765094504485 1.5663303 0.00000007176 0.0044660119488 0.9999900273188 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p171_45 : ‖exp (-((((((21171:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4619910892129:ℝ):ℂ) + ((0.8868845660445:ℝ):ℂ) * I)‖ ≤ 0.00000014444 := by
  have hl := lg_45
  refine (ecis_approx ((((21171:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.590851548914198827 80.59085159125626234 1.0905574 0.00000004443 0.4619910892129 0.8868845660445 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p171_46 : ‖exp (-((((((21171:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8108215022199:ℝ):ℂ) + ((0.5852935088806:ℝ):ℂ) * I)‖ ≤ 0.00000013716 := by
  have hl := lg_46
  refine (ecis_approx ((((21171:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 81.056166977554067586 81.056167030481631099 0.625242 0.00000003715 0.8108215022199 0.5852935088806 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p171_47 : ‖exp (-((((((21171:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9855959138863:ℝ):ℂ) + ((0.1691173986635:ℝ):ℂ) * I)‖ ≤ 0.00000014506 := by
  have hl := lg_47
  refine (ecis_approx ((((21171:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 81.511474848287075259 81.511474901214659943 0.1699341 0.00000004505 0.9855959138863 0.1691173986635 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p171_48 : ‖exp (-((((((21171:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.96221102878:ℝ):ℂ) + (((-0.2723048587413):ℝ):ℂ) * I)‖ ≤ 0.00000013402 := by
  have hl := lg_48
  refine (ecis_approx ((((21171:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 81.957196574414440044 81.957196627341961215 (-0.2757876) 0.00000003401 0.96221102878 (-0.2723048587413) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p171_49 : ‖exp (-((((((21171:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.756848562482:ℝ):ℂ) + (((-0.6535902795092):ℝ):ℂ) * I)‖ ≤ 0.00000015831 := by
  have hl := lg_49
  refine (ecis_approx ((((21171:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 82.393727509286838324 82.393727551628923008 (-0.7123185) 0.0000000583 0.756848562482 (-0.6535902795092) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p171_50 : ‖exp (-((((((21171:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.417567153901:ℝ):ℂ) + (((-0.9086460652988):ℝ):ℂ) * I)‖ ≤ 0.00000017295 := by
  have hl := lg_50
  refine (ecis_approx ((((21171:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 82.821439020402737478 82.82143907333027982 (-1.1400301) 0.00000007294 0.417567153901 (-0.9086460652988) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p201_2 : ‖exp (-((((((21201:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5296996974823):ℝ):ℂ) + (((-0.8481852571694):ℝ):ℂ) * I)‖ ≤ 0.00000014483 := by
  have hl := lg_2
  refine (ecis_approx ((((21201:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.6954133695403 14.6954133801408 (-2.1290428) 0.00000004482 (-0.5296996974823) (-0.8481852571694) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p201_3 : ‖exp (-((((((21201:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2669875717457):ℝ):ℂ) + ((0.963699972259:ℝ):ℂ) * I)‖ ≤ 0.00000010844 := by
  have hl := lg_3
  refine (ecis_approx ((((21201:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.291679126541484964 23.291679137142006165 1.8410621 0.00000000843 (-0.2669875717457) 0.963699972259 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p201_4 : ‖exp (-((((((21201:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4388365443791):ℝ):ℂ) + ((0.8985669075329:ℝ):ℂ) * I)‖ ≤ 0.0000001244 := by
  have hl := lg_4
  refine (ecis_approx ((((21201:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.3908267390806 29.3908267602816 2.0250998 0.00000002439 (-0.4388365443791) 0.8985669075329 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p201_5 : ‖exp (-((((((21201:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9065216253187):ℝ):ℂ) + (((-0.4221593806908):ℝ):ℂ) * I)‖ ≤ 0.00000015581 := by
  have hl := lg_5
  refine (ecis_approx ((((21201:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.121693170493145009 34.12169319169416621 (-2.7057666) 0.0000000558 (-0.9065216253187) (-0.4221593806908) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p201_6 : ‖exp (-((((((21201:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9588193447947:ℝ):ℂ) + (((-0.2840166615668):ℝ):ℂ) * I)‖ ≤ 0.00000014701 := by
  have hl := lg_6
  refine (ecis_approx ((((21201:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.987092496081784964 37.987092517282806165 (-0.2879807) 0.000000047 0.9588193447947 (-0.2840166615668) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p201_7 : ‖exp (-((((((21201:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.915303079096):ℝ):ℂ) + ((0.4027657796554:ℝ):ℂ) * I)‖ ≤ 0.00000013006 := by
  have hl := lg_7
  refine (ecis_approx ((((21201:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.255241059099481822 41.255241080300524224 2.7270561 0.00000003005 (-0.915303079096) 0.4027657796554 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p201_8 : ‖exp (-((((((21201:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9946027883575:ℝ):ℂ) + (((-0.1037559318379):ℝ):ℂ) * I)‖ ≤ 0.00000014165 := by
  have hl := lg_8
  refine (ecis_approx ((((21201:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.0862401086209 44.0862401404224 (-0.103943) 0.00000004164 0.9946027883575 (-0.1037559318379) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p201_9 : ‖exp (-((((((21201:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8574352693524):ℝ):ℂ) + (((-0.5145918370825):ℝ):ℂ) * I)‖ ≤ 0.00000012404 := by
  have hl := lg_9
  refine (ecis_approx ((((21201:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.583358253082969928 46.58335827428401233 (-2.6010611) 0.00000002403 (-0.8574352693524) (-0.5145918370825) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p201_10 : ‖exp (-((((((21201:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1221148749022:ℝ):ℂ) + ((0.9925159733362:ℝ):ℂ) * I)‖ ≤ 0.00000011742 := by
  have hl := lg_10
  refine (ecis_approx ((((21201:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.817106540033445009 48.81710657183496621 1.4483759 0.00000001741 0.1221148749022 0.9925159733362 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p201_11 : ‖exp (-((((((21201:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8406601952292:ℝ):ℂ) + (((-0.5415629567808):ℝ):ℂ) * I)‖ ≤ 0.00000013644 := by
  have hl := lg_11
  refine (ecis_approx ((((21201:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.837777662064918133 50.837777693866460535 (-0.5722952) 0.00000003643 0.8406601952292 (-0.5415629567808) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p201_12 : ‖exp (-((((((21201:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7487849957239):ℝ):ℂ) + (((-0.6628129676954):ℝ):ℂ) * I)‖ ≤ 0.00000014 := by
  have hl := lg_12
  refine (ecis_approx ((((21201:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.682505865622084964 52.682505897423606165 (-2.4170234) 0.00000003999 (-0.7487849957239) (-0.6628129676954) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p201_13 : ‖exp (-((((((21201:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5633047498451):ℝ):ℂ) + ((0.8262492110692:ℝ):ℂ) * I)‖ ≤ 0.00000015362 := by
  have hl := lg_13
  refine (ecis_approx ((((21201:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.3794913110087217 54.379491342810264102 2.1691764 0.00000005361 (-0.5633047498451) 0.8262492110692 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p201_14 : ‖exp (-((((((21201:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8264557605839:ℝ):ℂ) + ((0.5630016658925:ℝ):ℂ) * I)‖ ≤ 0.00000013599 := by
  have hl := lg_14
  refine (ecis_approx ((((21201:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.950654428639781822 55.950654460441324224 0.5980133 0.00000003598 0.8264557605839 0.5630016658925 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p201_15 : ‖exp (-((((((21201:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.648864991014:ℝ):ℂ) + (((-0.7609035572505):ℝ):ℂ) * I)‖ ≤ 0.00000016423 := by
  have hl := lg_15
  refine (ecis_approx ((((21201:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.413372297034629973 57.413372328836172375 (-0.8647045) 0.00000006422 0.648864991014 (-0.7609035572505) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p201_16 : ‖exp (-((((((21201:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6148449689717):ℝ):ℂ) + (((-0.788647997599):ℝ):ℂ) * I)‖ ≤ 0.00000015596 := by
  have hl := lg_16
  refine (ecis_approx ((((21201:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.7816534781612 58.7816535205632 (-2.2329857) 0.00000005595 (-0.6148449689717) (-0.788647997599) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p201_17 : ‖exp (-((((((21201:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9298852131122):ℝ):ℂ) + ((0.3678498202743:ℝ):ℂ) * I)‖ ≤ 0.00000015591 := by
  have hl := lg_17
  refine (ecis_approx ((((21201:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.066956085291417234 60.066956127693438435 2.764897 0.0000000559 (-0.9298852131122) 0.3678498202743 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p201_18 : ‖exp (-((((((21201:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0177140002637:ℝ):ℂ) + ((0.9998430947876:ℝ):ℂ) * I)‖ ≤ 0.00000014919 := by
  have hl := lg_18
  refine (ecis_approx ((((21201:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.278771622623269928 61.27877165442481233 1.5530814 0.00000004918 0.0177140002637 0.9998430947876 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p201_19 : ‖exp (-((((((21201:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9183907647854:ℝ):ℂ) + ((0.3956746177819:ℝ):ℂ) * I)‖ ≤ 0.0000001408 := by
  have hl := lg_19
  refine (ecis_approx ((((21201:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.425050780774370203 62.425050812575933806 0.4068023 0.00000004079 0.9183907647854 0.3956746177819 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p201_20 : ‖exp (-((((((21201:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7771532037994:ℝ):ℂ) + (((-0.6293114473966):ℝ):ℂ) * I)‖ ≤ 0.00000016224 := by
  have hl := lg_20
  refine (ecis_approx ((((21201:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.512519909573745009 63.51251995197576621 (-0.6806669) 0.00000006223 0.7771532037994 (-0.6293114473966) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p201_21 : ‖exp (-((((((21201:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1437708171358):ℝ):ℂ) + (((-0.9896110105185):ℝ):ℂ) * I)‖ ≤ 0.00000014566 := by
  have hl := lg_21
  refine (ecis_approx ((((21201:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.546920185640966786 64.546920217442530389 (-1.7150671) 0.00000004565 (-0.1437708171358) (-0.9896110105185) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p201_22 : ‖exp (-((((((21201:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.904643166835):ℝ):ℂ) + (((-0.426169849446):ℝ):ℂ) * I)‖ ≤ 0.00000014021 := by
  have hl := lg_22
  refine (ecis_approx ((((21201:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.533191031605218133 65.533191074007260535 (-2.701338) 0.0000000402 (-0.904643166835) (-0.426169849446) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p201_23 : ‖exp (-((((((21201:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.876541513095):ℝ):ℂ) + ((0.4813262674402:ℝ):ℂ) * I)‖ ≤ 0.00000012912 := by
  have hl := lg_23
  refine (ecis_approx ((((21201:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.475612849869448566 66.475612892271512169 2.6394255 0.00000002911 (-0.876541513095) 0.4813262674402 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p201_24 : ‖exp (-((((((21201:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.165556994681):ℝ):ℂ) + ((0.9862002238448:ℝ):ℂ) * I)‖ ≤ 0.00000014383 := by
  have hl := lg_24
  refine (ecis_approx ((((21201:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.377919235162384964 67.377919277564406165 1.7371191 0.00000004382 (-0.165556994681) 0.9862002238448 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p201_25 : ‖exp (-((((((21201:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6435629965112:ℝ):ℂ) + ((0.7653931470307:ℝ):ℂ) * I)‖ ≤ 0.000000138 := by
  have hl := lg_25
  refine (ecis_approx ((((21201:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.243386340986290018 68.24338638338833242 0.871652 0.00000003799 0.6435629965112 0.7653931470307 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p201_26 : ‖exp (-((((((21201:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9991947511563:ℝ):ℂ) + ((0.0401229268831:ℝ):ℂ) * I)‖ ≤ 0.00000014399 := by
  have hl := lg_26
  refine (ecis_approx ((((21201:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.0749046805490217 69.074904722951064102 0.0401337 0.00000004398 0.9991947511563 0.0401229268831 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p201_27 : ‖exp (-((((((21201:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.724836699662:ℝ):ℂ) + (((-0.6889207202742):ℝ):ℂ) * I)‖ ≤ 0.00000013247 := by
  have hl := lg_27
  refine (ecis_approx ((((21201:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.875037379624454892 69.875037411426018495 (-0.759999) 0.00000003246 0.724836699662 (-0.6889207202742) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p201_28 : ‖exp (-((((((21201:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0397564463311:ℝ):ℂ) + (((-0.9992093999633):ℝ):ℂ) * I)‖ ≤ 0.00000016162 := by
  have hl := lg_28
  refine (ecis_approx ((((21201:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.646067798180081822 70.646067840582124224 (-1.5310294) 0.00000006161 0.0397564463311 (-0.9992093999633) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p201_29 : ‖exp (-((((((21201:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6474275135047):ℝ):ℂ) + (((-0.7621270332041):ℝ):ℂ) * I)‖ ≤ 0.00000013294 := by
  have hl := lg_29
  refine (ecis_approx ((((21201:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.390038869498817092 71.390038911900880695 (-2.2750005) 0.00000003293 (-0.6474275135047) (-0.7621270332041) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p201_30 : ‖exp (-((((((21201:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9890907686659):ℝ):ℂ) + (((-0.1473073349936):ℝ):ℂ) * I)‖ ≤ 0.00000013002 := by
  have hl := lg_30
  refine (ecis_approx ((((21201:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 72.108785666574929973 72.108785708976972375 (-2.9937473) 0.00000003001 (-0.9890907686659) (-0.1473073349936) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p201_31 : ‖exp (-((((((21201:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8539161959599):ℝ):ℂ) + ((0.5204105400556:ℝ):ℂ) * I)‖ ≤ 0.00000015651 := by
  have hl := lg_31
  refine (ecis_approx ((((21201:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 72.803962700245140963 72.803962742647204566 2.594261 0.0000000565 (-0.8539161959599) 0.5204105400556 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p201_32 : ‖exp (-((((((21201:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3432364038626):ℝ):ℂ) + ((0.9392490463456:ℝ):ℂ) * I)‖ ≤ 0.00000013847 := by
  have hl := lg_32
  refine (ecis_approx ((((21201:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.4770668477015 73.477066900704 1.9211568 0.00000003846 (-0.3432364038626) 0.9392490463456 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p201_33 : ‖exp (-((((((21201:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2974583822391:ℝ):ℂ) + ((0.9547347856005:ℝ):ℂ) * I)‖ ≤ 0.00000014487 := by
  have hl := lg_33
  refine (ecis_approx ((((21201:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.129456788606403097 74.1294568310084667 1.2687669 0.00000004486 0.2974583822391 0.9547347856005 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p201_34 : ‖exp (-((((((21201:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.804564710589:ℝ):ℂ) + ((0.5938649901071:ℝ):ℂ) * I)‖ ≤ 0.00000013134 := by
  have hl := lg_34
  refine (ecis_approx ((((21201:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.762369454831717234 74.762369507834238435 0.6358542 0.00000003133 0.804564710589 0.5938649901071 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p201_35 : ‖exp (-((((((21201:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9997733892831:ℝ):ℂ) + ((0.0212877918403:ℝ):ℂ) * I)‖ ≤ 0.00000015658 := by
  have hl := lg_35
  refine (ecis_approx ((((21201:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.376934229592626831 75.376934271994690434 0.0212894 0.00000005657 0.9997733892831 0.0212877918403 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p201_36 : ‖exp (-((((((21201:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8386691263691:ℝ):ℂ) + (((-0.5446412548415):ℝ):ℂ) * I)‖ ≤ 0.00000014843 := by
  have hl := lg_36
  refine (ecis_approx ((((21201:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.974184992163569928 75.97418503456561233 (-0.5759613) 0.00000004842 0.8386691263691 (-0.5446412548415) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p201_37 : ‖exp (-((((((21201:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4022282198215:ℝ):ℂ) + (((-0.9155394361682):ℝ):ℂ) * I)‖ ≤ 0.00000014224 := by
  have hl := lg_37
  refine (ecis_approx ((((21201:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.555070643925774842 76.555070686327838445 (-1.156847) 0.00000004223 0.4022282198215 (-0.9155394361682) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p201_38 : ‖exp (-((((((21201:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1508659328373):ℝ):ℂ) + (((-0.9885542323558):ℝ):ℂ) * I)‖ ≤ 0.00000013586 := by
  have hl := lg_38
  refine (ecis_approx ((((21201:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.120464150314670203 77.120464192716733806 (-1.7222405) 0.00000003585 (-0.1508659328373) (-0.9885542323558) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p201_39 : ‖exp (-((((((21201:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6458609689951):ℝ):ℂ) + (((-0.7634550469493):ℝ):ℂ) * I)‖ ≤ 0.00000014862 := by
  have hl := lg_39
  refine (ecis_approx ((((21201:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.671170437550206664 77.671170479952270267 (-2.2729468) 0.00000004861 (-0.6458609689951) (-0.7634550469493) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p201_40 : ‖exp (-((((((21201:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9454304761532):ℝ):ℂ) + (((-0.3258239011628):ℝ):ℂ) * I)‖ ≤ 0.00000014598 := by
  have hl := lg_40
  refine (ecis_approx ((((21201:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 78.207933279114045009 78.20793333211656621 (-2.8097096) 0.00000004597 (-0.9454304761532) (-0.3258239011628) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p201_41 : ‖exp (-((((((21201:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9816960326506):ℝ):ℂ) + ((0.1904544542471:ℝ):ℂ) * I)‖ ≤ 0.00000013471 := by
  have hl := lg_41
  refine (ecis_approx ((((21201:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 78.73144135864250058 78.731441411645042982 2.9499676 0.0000000347 (-0.9816960326506) 0.1904544542471 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p201_42 : ‖exp (-((((((21201:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7632181064696):ℝ):ℂ) + ((0.6461409458622:ℝ):ℂ) * I)‖ ≤ 0.00000013817 := by
  have hl := lg_42
  refine (ecis_approx ((((21201:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.242333555181266786 79.242333597583330389 2.4390754 0.00000003816 (-0.7632181064696) 0.6461409458622 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p201_43 : ‖exp (-((((((21201:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3610643383959):ℝ):ℂ) + ((0.932540907165:ℝ):ℂ) * I)‖ ≤ 0.00000016257 := by
  have hl := lg_43
  refine (ecis_approx ((((21201:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.74120363077478978 79.741203673176874584 1.9402053 0.00000006256 (-0.3610643383959) 0.932540907165 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p201_44 : ‖exp (-((((((21201:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1177181362387:ℝ):ℂ) + ((0.9930470484324:ℝ):ℂ) * I)‖ ≤ 0.00000016083 := by
  have hl := lg_44
  refine (ecis_approx ((((21201:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.228604401145518133 80.228604454148060535 1.4528046 0.00000006082 0.1177181362387 0.9930470484324 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p201_45 : ‖exp (-((((((21201:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5600439315193:ℝ):ℂ) + ((0.828462910919:ℝ):ℂ) * I)‖ ≤ 0.00000016977 := by
  have hl := lg_45
  refine (ecis_approx ((((21201:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.705051423576114937 80.70505146597817854 0.9763575 0.00000006976 0.5600439315193 0.828462910919 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p201_46 : ‖exp (-((((((21201:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8725576183072:ℝ):ℂ) + ((0.4885112104488:ℝ):ℂ) * I)‖ ≤ 0.00000017394 := by
  have hl := lg_46
  refine (ecis_approx ((((21201:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 81.171026219409748566 81.171026272412312169 0.5103827 0.00000007393 0.8725576183072 0.4885112104488 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p201_47 : ‖exp (-((((((21201:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9985190695492:ℝ):ℂ) + ((0.0544028284796:ℝ):ℂ) * I)‖ ≤ 0.00000013598 := by
  have hl := lg_47
  refine (ecis_approx ((((21201:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 81.626979276299385129 81.626979329301969933 0.0544297 0.00000003597 0.9985190695492 0.0544028284796 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p201_48 : ‖exp (-((((((21201:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9241760186822:ℝ):ℂ) + (((-0.3819668657001):ℝ):ℂ) * I)‖ ≤ 0.00000016439 := by
  have hl := lg_48
  refine (ecis_approx ((((21201:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 82.073332604702684964 82.073332657705206165 (-0.3919236) 0.00000006438 0.9241760186822 (-0.3819668657001) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p201_49 : ‖exp (-((((((21201:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6755594586536:ℝ):ℂ) + (((-0.737305511863):ℝ):ℂ) * I)‖ ≤ 0.00000016728 := by
  have hl := lg_49
  refine (ecis_approx ((((21201:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 82.510482118198963644 82.510482160601048448 (-0.8290731) 0.00000006727 0.6755594586536 (-0.737305511863) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p201_50 : ‖exp (-((((((21201:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3083001538191:ℝ):ℂ) + (((-0.9512891333107):ℝ):ℂ) * I)‖ ≤ 0.00000017021 := by
  have hl := lg_50
  refine (ecis_approx ((((21201:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 82.938799710526590018 82.93879976352913242 (-1.2573907) 0.0000000702 0.3083001538191 (-0.9512891333107) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p231_2 : ‖exp (-((((((21231:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5472214111038):ℝ):ℂ) + (((-0.8369878895307):ℝ):ℂ) * I)‖ ≤ 0.00000012942 := by
  have hl := lg_2
  refine (ecis_approx ((((21231:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.7162077849493 14.7162077955648 (-2.1498372) 0.00000002941 (-0.5472214111038) (-0.8369878895307) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p231_3 : ‖exp (-((((((21231:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2350863172298):ℝ):ℂ) + ((0.971974497325:ℝ):ℂ) * I)‖ ≤ 0.00000013354 := by
  have hl := lg_3
  refine (ecis_approx ((((21231:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.324637495193729884 23.324637505809251115 1.8081037 0.00000003353 (-0.2350863172298) 0.971974497325 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p231_4 : ‖exp (-((((((21231:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4010975394851):ℝ):ℂ) + ((0.9160353507456:ℝ):ℂ) * I)‖ ≤ 0.00000015525 := by
  have hl := lg_4
  refine (ecis_approx ((((21231:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.4324155698986 29.4324155911296 1.983511 0.00000005524 (-0.4010975394851) 0.9160353507456 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p231_5 : ‖exp (-((((((21231:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9258404453679):ℝ):ℂ) + (((-0.3779146326468):ℝ):ℂ) * I)‖ ≤ 0.00000012806 := by
  have hl := lg_5
  refine (ecis_approx ((((21231:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.169976307850571279 34.16997632908159251 (-2.7540498) 0.00000002805 (-0.9258404453679) (-0.3779146326468) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p231_6 : ‖exp (-((((((21231:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9421751829567:ℝ):ℂ) + (((-0.3351207612496):ℝ):ℂ) * I)‖ ≤ 0.00000015831 := by
  have hl := lg_6
  refine (ecis_approx ((((21231:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.040845280143029884 38.040845301374051115 (-0.3417334) 0.0000000583 0.9421751829567 (-0.3351207612496) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p231_7 : ‖exp (-((((((21231:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8902448607576):ℝ):ℂ) + ((0.4554822584786:ℝ):ℂ) * I)‖ ≤ 0.00000013454 := by
  have hl := lg_7
  refine (ecis_approx ((((21231:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.313618363555544482 41.313618384786586944 2.6686788 0.00000003453 (-0.8902448607576) 0.4554822584786 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p231_8 : ‖exp (-((((((21231:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9861996565095:ℝ):ℂ) + (((-0.1655603741859):ℝ):ℂ) * I)‖ ≤ 0.00000013645 := by
  have hl := lg_8
  refine (ecis_approx ((((21231:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.1486233548479 44.1486233866944 (-0.1663262) 0.00000003644 0.9861996565095 (-0.1655603741859) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p231_9 : ‖exp (-((((((21231:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.889468843592):ℝ):ℂ) + (((-0.4569958163638):ℝ):ℂ) * I)‖ ≤ 0.00000015988 := by
  have hl := lg_9
  refine (ecis_approx ((((21231:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.649274990387459768 46.64927501161850223 (-2.6669779) 0.00000005987 (-0.889468843592) (-0.4569958163638) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p231_10 : ‖exp (-((((((21231:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1903297511756:ℝ):ℂ) + ((0.981720217688:ℝ):ℂ) * I)‖ ≤ 0.00000016465 := by
  have hl := lg_10
  refine (ecis_approx ((((21231:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.886184092799871279 48.88618412464639251 1.3792983 0.00000006464 0.1903297511756 0.981720217688 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p231_11 : ‖exp (-((((((21231:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7995611915758:ℝ):ℂ) + (((-0.6005846326089):ℝ):ℂ) * I)‖ ≤ 0.00000013723 := by
  have hl := lg_11
  refine (ecis_approx ((((21231:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.909714520225474123 50.909714552072016585 (-0.6442321) 0.00000003722 0.7995611915758 (-0.6005846326089) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p231_12 : ‖exp (-((((((21231:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7960704518131):ℝ):ℂ) + (((-0.6052039620676):ℝ):ℂ) * I)‖ ≤ 0.00000013952 := by
  have hl := lg_12
  refine (ecis_approx ((((21231:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.757053065092329884 52.757053096938851115 (-2.4915706) 0.00000003951 (-0.7960704518131) (-0.6052039620676) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p231_13 : ‖exp (-((((((21231:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.498122061661):ℝ):ℂ) + ((0.8671069205585:ℝ):ℂ) * I)‖ ≤ 0.00000015895 := by
  have hl := lg_13
  refine (ecis_approx ((((21231:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.4564397917091727 54.456439823555715162 2.092228 0.00000005894 (-0.498122061661) 0.8671069205585 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p231_14 : ‖exp (-((((((21231:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8683941832415:ℝ):ℂ) + ((0.4958745229515:ℝ):ℂ) * I)‖ ≤ 0.00000011613 := by
  have hl := lg_14
  refine (ecis_approx ((((21231:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 56.029826148504844482 56.029826180351386944 0.5188416 0.00000001612 0.8683941832415 0.4958745229515 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p231_15 : ‖exp (-((((((21231:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5849758058328:ℝ):ℂ) + (((-0.811050742303):ℝ):ℂ) * I)‖ ≤ 0.00000016159 := by
  have hl := lg_15
  refine (ecis_approx ((((21231:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.494613803044301163 57.494613834890843625 (-0.9459461) 0.00000006158 0.5849758058328 (-0.811050742303) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p231_16 : ‖exp (-((((((21231:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6782415958436):ℝ):ℂ) + (((-0.734838987566):ℝ):ℂ) * I)‖ ≤ 0.00000012483 := by
  have hl := lg_16
  refine (ecis_approx ((((21231:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.8648311397972 58.8648311822592 (-2.3161634) 0.00000002482 (-0.6782415958436) (-0.734838987566) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p231_17 : ‖exp (-((((((21231:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8953000311446):ℝ):ℂ) + ((0.4454636395053:ℝ):ℂ) * I)‖ ≤ 0.00000015626 := by
  have hl := lg_17
  refine (ecis_approx ((((21231:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.151952485581910254 60.151952528043931485 2.6799006 0.00000005625 (-0.8953000311446) 0.4454636395053 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p231_18 : ‖exp (-((((((21231:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1042363395124:ℝ):ℂ) + ((0.9945525554363:ℝ):ℂ) * I)‖ ≤ 0.0000001354 := by
  have hl := lg_18
  refine (ecis_approx ((((21231:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.365482775336759768 61.36548280718330223 1.4663703 0.00000003539 0.1042363395124 0.9945525554363 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p231_19 : ‖exp (-((((((21231:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9497158755021:ℝ):ℂ) + ((0.3131130080646:ℝ):ℂ) * I)‖ ≤ 0.00000012168 := by
  have hl := lg_19
  refine (ecis_approx ((((21231:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.513383950125968293 62.513383981972531986 0.3184691 0.00000002167 0.9497158755021 0.3131130080646 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p231_20 : ‖exp (-((((((21231:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7175354877558:ℝ):ℂ) + (((-0.6965219478315):ℝ):ℂ) * I)‖ ≤ 0.00000014843 := by
  have hl := lg_20
  refine (ecis_approx ((((21231:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.602391877749171279 63.60239192021119251 (-0.7705388) 0.00000004842 0.7175354877558 (-0.6965219478315) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p231_21 : ‖exp (-((((((21231:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.233432746545):ℝ):ℂ) + (((-0.9723729494589):ℝ):ℂ) * I)‖ ≤ 0.00000011881 := by
  have hl := lg_21
  refine (ecis_approx ((((21231:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.638255858749274366 64.638255890595838059 (-1.8064028) 0.0000000188 (-0.233432746545) (-0.9723729494589) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p231_22 : ‖exp (-((((((21231:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9402190675915):ℝ):ℂ) + (((-0.3405702640536):ℝ):ℂ) * I)‖ ≤ 0.00000016664 := by
  have hl := lg_22
  refine (ecis_approx ((((21231:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.625922305174774123 65.625922347636816585 (-2.7940693) 0.00000006663 (-0.9402190675915) (-0.3405702640536) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p231_23 : ‖exp (-((((((21231:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8274573497838):ℝ):ℂ) + ((0.5615285693779:ℝ):ℂ) * I)‖ ≤ 0.00000013982 := by
  have hl := lg_23
  refine (ecis_approx ((((21231:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.569677676316129546 66.569677718778193239 2.5453607 0.00000003981 (-0.8274573497838) 0.5615285693779 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p231_24 : ‖exp (-((((((21231:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0709215838257):ℝ):ℂ) + ((0.9974818940448:ℝ):ℂ) * I)‖ ≤ 0.00000012895 := by
  have hl := lg_24
  refine (ecis_approx ((((21231:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.473260850041629884 67.473260892503651115 1.6417775 0.00000002894 (-0.0709215838257) 0.9974818940448 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p231_25 : ‖exp (-((((((21231:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7143610657648:ℝ):ℂ) + ((0.6997772986596:ℝ):ℂ) * I)‖ ≤ 0.00000016329 := by
  have hl := lg_25
  refine (ecis_approx ((((21231:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.339952615701142558 68.33995265816318502 0.7750857 0.00000006328 0.7143610657648 0.6997772986596 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p231_26 : ‖exp (-((((((21231:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9983410489271:ℝ):ℂ) + (((-0.0575773395273):ℝ):ℂ) * I)‖ ≤ 0.00000014016 := by
  have hl := lg_26
  refine (ecis_approx ((((21231:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.1726475766584727 69.172647619120515162 (-0.0576092) 0.00000004015 0.9983410489271 (-0.0575773395273) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p231_27 : ‖exp (-((((((21231:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6532903093939:ℝ):ℂ) + (((-0.7571075033653):ℝ):ℂ) * I)‖ ≤ 0.00000013847 := by
  have hl := lg_27
  refine (ecis_approx ((((21231:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.973912485581189652 69.973912517427753345 (-0.8588741) 0.00000003846 0.6532903093939 (-0.7571075033653) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p231_28 : ‖exp (-((((((21231:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0601629199085):ℝ):ℂ) + (((-0.9981885708962):ℝ):ℂ) * I)‖ ≤ 0.00000014554 := by
  have hl := lg_28
  refine (ecis_approx ((((21231:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.746033933454144482 70.746033975916186944 (-1.6309956) 0.00000004553 (-0.0601629199085) (-0.9981885708962) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p231_29 : ‖exp (-((((((21231:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7209852396036):ℝ):ℂ) + (((-0.6929504197606):ℝ):ℂ) * I)‖ ≤ 0.00000013462 := by
  have hl := lg_29
  refine (ecis_approx ((((21231:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.491057744367217852 71.491057786829281545 (-2.3760194) 0.00000003461 (-0.7209852396036) (-0.6929504197606) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p231_30 : ‖exp (-((((((21231:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9989509301776):ℝ):ℂ) + (((-0.0457934331029):ℝ):ℂ) * I)‖ ≤ 0.0000001515 := by
  have hl := lg_30
  refine (ecis_approx ((((21231:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 72.210821587993601163 72.210821630455643625 (-3.0957832) 0.00000005149 (-0.9989509301776) (-0.0457934331029) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p231_31 : ‖exp (-((((((21231:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7958711149896):ℝ):ℂ) + ((0.605466075249:ℝ):ℂ) * I)‖ ≤ 0.00000016982 := by
  have hl := lg_31
  refine (ecis_approx ((((21231:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 72.906982316348501853 72.906982358810565546 2.4912413 0.00000006981 (-0.7958711149896) 0.605466075249 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p231_32 : ‖exp (-((((((21231:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2439030032499):ℝ):ℂ) + ((0.9697996313695:ℝ):ℂ) * I)‖ ≤ 0.00000016142 := by
  have hl := lg_32
  refine (ecis_approx ((((21231:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.5810389247465 73.581038977824 1.8171847 0.00000006141 (-0.2439030032499) 0.9697996313695 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p231_33 : ‖exp (-((((((21231:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3957870504542:ℝ):ℂ) + ((0.9183423167277:ℝ):ℂ) * I)‖ ≤ 0.00000017075 := by
  have hl := lg_33
  refine (ecis_approx ((((21231:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.234352015419204007 74.2343520578812677 1.1638716 0.00000007074 0.3957870504542 0.9183423167277 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p231_34 : ‖exp (-((((((21231:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8627750179669:ℝ):ℂ) + ((0.5055880421571:ℝ):ℂ) * I)‖ ≤ 0.00000013747 := by
  have hl := lg_34
  refine (ecis_approx ((((21231:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.868160270531210254 74.868160323608731485 0.5300634 0.00000003746 0.8627750179669 0.5055880421571 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p231_35 : ‖exp (-((((((21231:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9963581088907:ℝ):ℂ) + (((-0.0852673375205):ℝ):ℂ) * I)‖ ≤ 0.00000012773 := by
  have hl := lg_35
  refine (ecis_approx ((((21231:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.483594671406115761 75.483594713868179454 (-0.085371) 0.00000002772 0.9963581088907 (-0.0852673375205) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p231_36 : ‖exp (-((((((21231:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7753880876105:ℝ):ℂ) + (((-0.6314850066246):ℝ):ℂ) * I)‖ ≤ 0.00000012588 := by
  have hl := lg_36
  refine (ecis_approx ((((21231:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.081690560286059768 76.08169060274810223 (-0.6834669) 0.00000002587 0.7753880876105 (-0.6314850066246) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p231_37 : ‖exp (-((((((21231:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3008862447074:ℝ):ℂ) + (((-0.9536600378258):ℝ):ℂ) * I)‖ ≤ 0.0000001376 := by
  have hl := lg_37
  refine (ecis_approx ((((21231:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.663398181273908102 76.663398223735971795 (-1.2651745) 0.00000003759 0.3008862447074 (-0.9536600378258) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p231_38 : ‖exp (-((((((21231:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2576330657344):ℝ):ℂ) + (((-0.9662428284024):ℝ):ℂ) * I)‖ ≤ 0.00000015109 := by
  have hl := lg_38
  refine (ecis_approx ((((21231:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.229591735075268293 77.229591777537331986 (-1.8313681) 0.00000005108 (-0.2576330657344) (-0.9662428284024) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p231_39 : ‖exp (-((((((21231:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7257041272901):ℝ):ℂ) + (((-0.6880069182833):ℝ):ℂ) * I)‖ ≤ 0.00000014322 := by
  have hl := lg_39
  refine (ecis_approx ((((21231:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.781077286902902584 77.781077329364966277 (-2.3828536) 0.00000004321 (-0.7257041272901) (-0.6880069182833) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p231_40 : ‖exp (-((((((21231:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9756312171381):ℝ):ℂ) + (((-0.2194167902569):ℝ):ℂ) * I)‖ ≤ 0.00000012964 := by
  have hl := lg_40
  refine (ecis_approx ((((21231:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 78.318599662698471279 78.31859971577599251 (-2.920376) 0.00000002963 (-0.9756312171381) (-0.2194167902569) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p272_2 : ‖exp (-((((((21272:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.570783604307):ℝ):ℂ) + (((-0.8211005279772):ℝ):ℂ) * I)‖ ≤ 0.00000011563 := by
  have hl := lg_2
  refine (ecis_approx ((((21272:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.7446268193416 14.7446268299776 (-2.1782562) 0.00000001562 (-0.570783604307) (-0.8211005279772) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p272_3 : ‖exp (-((((((21272:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1910819348202):ℝ):ℂ) + ((0.9815740900128:ℝ):ℂ) * I)‖ ≤ 0.00000012971 := by
  have hl := lg_3
  refine (ecis_approx ((((21272:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.369680599018464608 23.36968060965448588 1.7630606 0.0000000297 (-0.1910819348202) 0.9815740900128 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p272_4 : ‖exp (-((((((21272:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3484121473778):ℝ):ℂ) + ((0.9373414402219:ℝ):ℂ) * I)‖ ≤ 0.00000012407 := by
  have hl := lg_4
  refine (ecis_approx ((((21272:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.4892536386832 29.4892536599552 1.9266729 0.00000002406 (-0.3484121473778) 0.9373414402219 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p272_5 : ‖exp (-((((((21272:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9487448181946):ℝ):ℂ) + (((-0.3160431453912):ℝ):ℂ) * I)‖ ≤ 0.00000014763 := by
  have hl := lg_5
  refine (ecis_approx ((((21272:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.235963262239053848 34.23596328351107512 (-2.8200367) 0.00000004762 (-0.9487448181946) (-0.3160431453912) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p272_6 : ‖exp (-((((((21272:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9150374390389:ℝ):ℂ) + (((-0.4033689194239):ℝ):ℂ) * I)‖ ≤ 0.00000012473 := by
  have hl := lg_6
  refine (ecis_approx ((((21272:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.114307418360064608 38.11430743963208588 (-0.4151956) 0.00000002472 0.9150374390389 (-0.4033689194239) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p272_7 : ‖exp (-((((((21272:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8511121800973):ℝ):ℂ) + ((0.5249838633859:ℝ):ℂ) * I)‖ ≤ 0.00000015068 := by
  have hl := lg_7
  refine (ecis_approx ((((21272:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.393400679645496784 41.393400700917539328 2.5888965 0.00000005067 (-0.8511121800973) 0.5249838633859 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p272_8 : ‖exp (-((((((21272:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9685194927322:ℝ):ℂ) + (((-0.24893772755):ℝ):ℂ) * I)‖ ≤ 0.00000013969 := by
  have hl := lg_8
  refine (ecis_approx ((((21272:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.2338804580248 44.2338804899328 (-0.2515833) 0.00000003968 0.9685194927322 (-0.24893772755) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p272_9 : ‖exp (-((((((21272:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9269753856274):ℝ):ℂ) + (((-0.3751221591516):ℝ):ℂ) * I)‖ ≤ 0.00000015224 := by
  have hl := lg_9
  refine (ecis_approx ((((21272:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.739361198036929216 46.73936121930897176 (-2.7570641) 0.00000005223 (-0.9269753856274) (-0.3751221591516) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p272_10 : ‖exp (-((((((21272:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2820248001945:ℝ):ℂ) + ((0.9594071148763:ℝ):ℂ) * I)‖ ≤ 0.00000015607 := by
  have hl := lg_10
  refine (ecis_approx ((((21272:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.980590081580653848 48.98059011348867512 1.2848924 0.00000005606 0.2820248001945 0.9594071148763 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p272_11 : ‖exp (-((((((21272:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7367495653763:ℝ):ℂ) + (((-0.6761657177925):ℝ):ℂ) * I)‖ ≤ 0.00000013107 := by
  have hl := lg_11
  refine (ecis_approx ((((21272:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.008028226378233976 51.00802825828627652 (-0.7425458) 0.00000003106 0.7367495653763 (-0.6761657177925) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p272_12 : ‖exp (-((((((21272:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8534948002228):ℝ):ℂ) + (((-0.5211013585825):ℝ):ℂ) * I)‖ ≤ 0.00000011975 := by
  have hl := lg_12
  refine (ecis_approx ((((21272:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.858934237701664608 52.85893426960968588 (-2.5934518) 0.00000001974 (-0.8534948002228) (-0.5211013585825) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p272_13 : ‖exp (-((((((21272:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4043505891562):ℝ):ℂ) + ((0.9146040679145:ℝ):ℂ) * I)‖ ≤ 0.0000001493 := by
  have hl := lg_13
  refine (ecis_approx ((((21272:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.5616027153331224 54.561602747241164944 1.987065 0.00000004929 (-0.4043505891562) 0.9146040679145 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p272_14 : ‖exp (-((((((21272:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9168654451985:ℝ):ℂ) + ((0.3991963870089:ℝ):ℂ) * I)‖ ≤ 0.00000016564 := by
  have hl := lg_14
  refine (ecis_approx ((((21272:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 56.138027498987096784 56.138027530895139328 0.4106402 0.00000006563 0.9168654451985 0.3991963870089 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p272_15 : ‖exp (-((((((21272:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.491507758469:ℝ):ℂ) + (((-0.8708731959159):ℝ):ℂ) * I)‖ ≤ 0.00000012856 := by
  have hl := lg_15
  refine (ecis_approx ((((21272:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.605643861257518456 57.605643893165561 (-1.0569761) 0.00000002855 0.491507758469 (-0.8708731959159) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p272_16 : ‖exp (-((((((21272:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7572179464238):ℝ):ℂ) + (((-0.6531622934448):ℝ):ℂ) * I)‖ ≤ 0.00000015531 := by
  have hl := lg_16
  refine (ecis_approx ((((21272:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.9785072773664 58.9785073199104 (-2.4298395) 0.0000000553 (-0.7572179464238) (-0.6531622934448) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p272_17 : ‖exp (-((((((21272:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8376368622518):ℝ):ℂ) + ((0.5462275047362:ℝ):ℂ) * I)‖ ≤ 0.00000013917 := by
  have hl := lg_17
  refine (ecis_approx ((((21272:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.268114232645584048 60.26811427518960532 2.5637388 0.00000003916 (-0.8376368622518) 0.5462275047362 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p272_18 : ‖exp (-((((((21272:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2210893557387:ℝ):ℂ) + ((0.9752535551225:ℝ):ℂ) * I)‖ ≤ 0.00000015443 := by
  have hl := lg_18
  refine (ecis_approx ((((21272:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.483988017378529216 61.48398804928657176 1.347865 0.00000005442 0.2210893557387 0.9752535551225 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p272_19 : ‖exp (-((((((21272:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9805116724064:ℝ):ℂ) + ((0.196460836491:ℝ):ℂ) * I)‖ ≤ 0.00000012357 := by
  have hl := lg_19
  refine (ecis_approx ((((21272:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.634105948239819016 62.634105980147882832 0.1977471 0.00000002356 0.9805116724064 0.196460836491 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p272_20 : ‖exp (-((((((21272:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6267944786978:ℝ):ℂ) + (((-0.7791846260508):ℝ):ℂ) * I)‖ ≤ 0.00000017089 := by
  have hl := lg_20
  refine (ecis_approx ((((21272:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.725216900922253848 63.72521694346627512 (-0.8933639) 0.00000007088 0.6267944786978 (-0.7791846260508) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p272_21 : ‖exp (-((((((21272:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3526783891714):ℝ):ℂ) + (((-0.9357445986):ℝ):ℂ) * I)‖ ≤ 0.00000013879 := by
  have hl := lg_21
  refine (ecis_approx ((((21272:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.763081278663961392 64.763081310572025208 (-1.9312282) 0.00000003878 (-0.3526783891714) (-0.9357445986) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p272_22 : ‖exp (-((((((21272:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9757246001609):ℝ):ℂ) + (((-0.2190011514613):ℝ):ℂ) * I)‖ ≤ 0.00000012609 := by
  have hl := lg_22
  refine (ecis_approx ((((21272:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.752655045719833976 65.75265508826387652 (-2.920802) 0.00000002608 (-0.9757246001609) (-0.2190011514613) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p272_23 : ‖exp (-((((((21272:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7486404847055):ℝ):ℂ) + ((0.6629761870735:ℝ):ℂ) * I)‖ ≤ 0.00000013986 := by
  have hl := lg_23
  refine (ecis_approx ((((21272:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.698232939126593552 66.698232981670657368 2.4168054 0.00000003985 (-0.7486404847055) 0.6629761870735 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p272_24 : ‖exp (-((((((21272:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0592842448075:ℝ):ℂ) + ((0.9982411423686:ℝ):ℂ) * I)‖ ≤ 0.00000012195 := by
  have hl := lg_24
  refine (ecis_approx ((((21272:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.603561057043264608 67.60356109958728588 1.5114773 0.00000002194 0.0592842448075 0.9982411423686 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p272_25 : ‖exp (-((((((21272:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8002335246455:ℝ):ℂ) + ((0.5996885075048:ℝ):ℂ) * I)‖ ≤ 0.00000015451 := by
  have hl := lg_25
  refine (ecis_approx ((((21272:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.471926524478107696 68.47192656702215024 0.6431118 0.0000000545 0.8002335246455 0.5996885075048 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p272_26 : ‖exp (-((((((21272:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9817785697438:ℝ):ℂ) + (((-0.1900285241534):ℝ):ℂ) * I)‖ ≤ 0.00000014432 := by
  have hl := lg_26
  refine (ecis_approx ((((21272:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.3062295346747224 69.306229577218764944 (-0.1911912) 0.00000004431 0.9817785697438 (-0.1900285241534) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p272_27 : ‖exp (-((((((21272:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5453385261409:ℝ):ℂ) + (((-0.8382158981471):ℝ):ℂ) * I)‖ ≤ 0.00000015 := by
  have hl := lg_27
  refine (ecis_approx ((((21272:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.109041797055393824 70.10904182896345764 (-0.9940034) 0.00000004999 0.5453385261409 (-0.8382158981471) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p272_28 : ‖exp (-((((((21272:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1955513993337):ℝ):ℂ) + (((-0.9806934537447):ℝ):ℂ) * I)‖ ≤ 0.00000016066 := by
  have hl := lg_28
  refine (ecis_approx ((((21272:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.882654318328696784 70.882654360872739328 (-1.767616) 0.00000006065 (-0.1955513993337) (-0.9806934537447) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p272_29 : ‖exp (-((((((21272:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8094895335998):ℝ):ℂ) + (((-0.5871343074113):ℝ):ℂ) * I)‖ ≤ 0.00000013694 := by
  have hl := lg_29
  refine (ecis_approx ((((21272:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.629116873354032224 71.62911691589809604 (-2.5140785) 0.00000003693 (-0.8094895335998) (-0.5871343074113) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p272_30 : ‖exp (-((((((21272:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9956190100021):ℝ):ℂ) + ((0.0935028685927:ℝ):ℂ) * I)‖ ≤ 0.000000137 := by
  have hl := lg_30
  refine (ecis_approx ((((21272:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 72.350270680599118456 72.350270723143161 3.047953 0.00000003699 (-0.9956190100021) 0.0935028685927 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p272_31 : ‖exp (-((((((21272:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7030316751871):ℝ):ℂ) + ((0.7111585362346:ℝ):ℂ) * I)‖ ≤ 0.00000014809 := by
  have hl := lg_31
  refine (ecis_approx ((((21272:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.047775791689761736 73.047775834233825552 2.3504479 0.00000004808 (-0.7030316751871) 0.7111585362346 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p272_32 : ‖exp (-((((((21272:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1041043081724):ℝ):ℂ) + ((0.9945663844206:ℝ):ℂ) * I)‖ ≤ 0.00000016375 := by
  have hl := lg_32
  refine (ecis_approx ((((21272:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.723134096708 73.723134149888 1.6750896 0.00000006374 (-0.1041043081724) 0.9945663844206 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p272_33 : ‖exp (-((((((21272:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5229272167104:ℝ):ℂ) + ((0.8523773378167:ℝ):ℂ) * I)‖ ≤ 0.00000016077 := by
  have hl := lg_33
  refine (ecis_approx ((((21272:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.377708825396698584 74.3777088679407624 1.0205148 0.00000006076 0.5229272167104 0.8523773378167 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p272_34 : ‖exp (-((((((21272:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9266170799139:ℝ):ℂ) + ((0.3760063659194:ℝ):ℂ) * I)‖ ≤ 0.00000013418 := by
  have hl := lg_34
  refine (ecis_approx ((((21272:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.012741051987184048 75.01274110516720532 0.3854826 0.00000003417 0.9266170799139 0.3760063659194 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p272_35 : ‖exp (-((((((21272:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9734057992702:ℝ):ℂ) + (((-0.229087646867):ℝ):ℂ) * I)‖ ≤ 0.00000014429 := by
  have hl := lg_35
  refine (ecis_approx ((((21272:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.629363941884550632 75.629363984428614448 (-0.2311403) 0.00000004428 0.9734057992702 (-0.229087646867) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p272_36 : ‖exp (-((((((21272:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6745870296856:ℝ):ℂ) + (((-0.738195326035):ℝ):ℂ) * I)‖ ≤ 0.00000014945 := by
  have hl := lg_36
  refine (ecis_approx ((((21272:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.228614836720129216 76.22861487926417176 (-0.8303912) 0.00000004944 0.6745870296856 (-0.738195326035) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p272_37 : ‖exp (-((((((21272:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1569228519666:ℝ):ℂ) + (((-0.9876108639189):ℝ):ℂ) * I)‖ ≤ 0.00000017052 := by
  have hl := lg_37
  refine (ecis_approx ((((21272:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.811445815649690224 76.81144585819375404 (-1.4132222) 0.00000007051 0.1569228519666 (-0.9876108639189) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p272_38 : ‖exp (-((((((21272:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3983458898712):ℝ):ℂ) + (((-0.917235276262):ℝ):ℂ) * I)‖ ≤ 0.00000012399 := by
  have hl := lg_38
  refine (ecis_approx ((((21272:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.378732767581419016 77.378732810125482832 (-1.9805091) 0.00000002398 (-0.3983458898712) (-0.917235276262) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p272_39 : ‖exp (-((((((21272:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8204875014823):ℝ):ℂ) + (((-0.5716644643963):ℝ):ℂ) * I)‖ ≤ 0.00000017076 := by
  have hl := lg_39
  refine (ecis_approx ((((21272:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.931283314351587008 77.931283356895650824 (-2.5330596) 0.00000007075 (-0.8204875014823) (-0.5716644643963) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p272_40 : ‖exp (-((((((21272:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9975529193081):ℝ):ℂ) + (((-0.069915467871):ℝ):ℂ) * I)‖ ≤ 0.00000016591 := by
  have hl := lg_40
  refine (ecis_approx ((((21272:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 78.469843720263853848 78.46984377344387512 (-3.0716201) 0.0000000659 (-0.9975529193081) (-0.069915467871) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p327_2 : ‖exp (-((((((21327:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6016641900781):ℝ):ℂ) + (((-0.7987491485852):ℝ):ℂ) * I)‖ ≤ 0.00000011058 := by
  have hl := lg_2
  refine (ecis_approx ((((21327:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.7827499142581 14.7827499249216 (-2.2163793) 0.00000001057 (-0.6016641900781) (-0.7987491485852) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p327_3 : ‖exp (-((((((21327:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1314589642607):ℝ):ℂ) + ((0.9913216131584:ℝ):ℂ) * I)‖ ≤ 0.00000015385 := by
  have hl := lg_3
  refine (ecis_approx ((((21327:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.430104274880913628 23.430104285544434955 1.7026369 0.00000005384 (-0.1314589642607) 0.9913216131584 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p327_4 : ‖exp (-((((((21327:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2760003978525):ℝ):ℂ) + ((0.9611575211087:ℝ):ℂ) * I)‖ ≤ 0.00000011396 := by
  have hl := lg_4
  refine (ecis_approx ((((21327:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.5654998285162 29.5654998498432 1.8504267 0.00000001395 (-0.2760003978525) 0.9611575211087 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p327_5 : ‖exp (-((((((21327:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9729695717903):ℝ):ℂ) + (((-0.2309333498757):ℝ):ℂ) * I)‖ ≤ 0.00000013284 := by
  have hl := lg_5
  refine (ecis_approx ((((21327:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.324482347394335343 34.32448236872135667 (-2.9085558) 0.00000003283 (-0.9729695717903) (-0.2309333498757) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p327_6 : ‖exp (-((((((21327:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8709114457519:ℝ):ℂ) + (((-0.4914399797109):ℝ):ℂ) * I)‖ ≤ 0.00000015395 := by
  have hl := lg_6
  refine (ecis_approx ((((21327:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.212854189139013628 38.212854210466034955 (-0.5137424) 0.00000005394 0.8709114457519 (-0.4914399797109) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p327_7 : ‖exp (-((((((21327:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7901631049166):ℝ):ℂ) + ((0.6128966206326:ℝ):ℂ) * I)‖ ≤ 0.00000011246 := by
  have hl := lg_7
  refine (ecis_approx ((((21327:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.500425737814944994 41.500425759141987648 2.4818714 0.00000001245 (-0.7901631049166) 0.6128966206326 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p327_8 : ‖exp (-((((((21327:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9337833074844:ℝ):ℂ) + (((-0.357838978681):ℝ):ℂ) * I)‖ ≤ 0.00000012452 := by
  have hl := lg_8
  refine (ecis_approx ((((21327:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.3482497427743 44.3482497747648 (-0.3659526) 0.00000002451 0.9337833074844 (-0.357838978681) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p327_9 : ‖exp (-((((((21327:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9654370533999):ℝ):ℂ) + (((-0.2606363283768):ℝ):ℂ) * I)‖ ≤ 0.00000012085 := by
  have hl := lg_9
  refine (ecis_approx ((((21327:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.860208549761827256 46.86020857108886991 (-2.8779114) 0.00000002084 (-0.9654370533999) (-0.2606363283768) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p327_10 : ‖exp (-((((((21327:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4009431393186:ℝ):ℂ) + ((0.9161029412862:ℝ):ℂ) * I)‖ ≤ 0.00000013622 := by
  have hl := lg_10
  refine (ecis_approx ((((21327:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.107232261652435343 49.10723229364295667 1.1582502 0.00000003621 0.4009431393186 0.9161029412862 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p327_11 : ‖exp (-((((((21327:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.641434253806:ℝ):ℂ) + (((-0.7671780093592):ℝ):ℂ) * I)‖ ≤ 0.00000014091 := by
  have hl := lg_11
  refine (ecis_approx ((((21327:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.139912466339253291 51.139912498329795945 (-0.87443) 0.0000000409 0.641434253806 (-0.7671780093592) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p327_12 : ‖exp (-((((((21327:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9165334949741):ℝ):ℂ) + (((-0.3999579383546):ℝ):ℂ) * I)‖ ≤ 0.00000015405 := by
  have hl := lg_12
  refine (ecis_approx ((((21327:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.995604103397113628 52.995604135387634955 (-2.7301217) 0.00000005404 (-0.9165334949741) (-0.3999579383546) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p327_13 : ‖exp (-((((((21327:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2717360224772):ℝ):ℂ) + ((0.9623718273551:ℝ):ℂ) * I)‖ ≤ 0.00000013468 := by
  have hl := lg_13
  refine (ecis_approx ((((21327:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.7026749299506159 54.702674961941158554 1.8459928 0.00000003467 (-0.2717360224772) 0.9623718273551 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p327_14 : ‖exp (-((((((21327:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9649634984811:ℝ):ℂ) + ((0.2623841584378:ℝ):ℂ) * I)‖ ≤ 0.00000011946 := by
  have hl := lg_14
  refine (ecis_approx ((((21327:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 56.283175652073044994 56.283175684063587648 0.2654921 0.00000001945 0.9649634984811 0.2623841584378 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p327_15 : ‖exp (-((((((21327:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3568347932524:ℝ):ℂ) + (((-0.9341675065664):ℝ):ℂ) * I)‖ ≤ 0.00000014236 := by
  have hl := lg_15
  refine (ecis_approx ((((21327:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.754586622275248971 57.754586654265791625 (-1.2059189) 0.00000004235 0.3568347932524 (-0.9341675065664) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p327_16 : ‖exp (-((((((21327:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8476475569438):ℝ):ℂ) + (((-0.5305597224959):ℝ):ℂ) * I)‖ ≤ 0.00000013509 := by
  have hl := lg_16
  refine (ecis_approx ((((21327:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 59.1309996570324 59.1309996996864 (-2.5823319) 0.00000003508 (-0.8476475569438) (-0.5305597224959) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p327_17 : ‖exp (-((((((21327:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7427149112147):ℝ):ℂ) + ((0.6696077662537:ℝ):ℂ) * I)‖ ≤ 0.00000013738 := by
  have hl := lg_17
  refine (ecis_approx ((((21327:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.423940966511487918 60.423941009165509245 2.4079121 0.00000003737 (-0.7427149112147) 0.6696077662537 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p327_18 : ‖exp (-((((((21327:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3726858640407:ℝ):ℂ) + ((0.9279575673188:ℝ):ℂ) * I)‖ ≤ 0.00000012423 := by
  have hl := lg_18
  refine (ecis_approx ((((21327:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.642958464019927256 61.64295849601046991 1.1888946 0.00000002422 0.3726858640407 0.9279575673188 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p327_19 : ‖exp (-((((((21327:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9993591410572:ℝ):ℂ) + ((0.0357953514489:ℝ):ℂ) * I)‖ ≤ 0.00000015226 := by
  have hl := lg_19
  refine (ecis_approx ((((21327:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.796050092051082181 62.796050124041646162 0.035803 0.00000005225 0.9993591410572 0.0357953514489 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p327_20 : ‖exp (-((((((21327:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4905033151892:ℝ):ℂ) + (((-0.8714393253626):ℝ):ℂ) * I)‖ ≤ 0.00000014678 := by
  have hl := lg_20
  refine (ecis_approx ((((21327:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.889982175910535343 63.88998221856455667 (-1.0581291) 0.00000004677 0.4905033151892 (-0.8714393253626) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p327_21 : ‖exp (-((((((21327:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5037036371175):ℝ):ℂ) + (((-0.8638765223967):ℝ):ℂ) * I)‖ ≤ 0.00000015912 := by
  have hl := lg_21
  refine (ecis_approx ((((21327:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.930530012695858622 64.930530044686422603 (-2.098677) 0.00000005911 (-0.5037036371175) (-0.8638765223967) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p327_22 : ‖exp (-((((((21327:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9987108023266):ℝ):ℂ) + (((-0.0507615281964):ℝ):ℂ) * I)‖ ≤ 0.00000015147 := by
  have hl := lg_22
  refine (ecis_approx ((((21327:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.922662380597353291 65.922662423251395945 (-3.0908093) 0.00000005146 (-0.9987108023266) (-0.0507615281964) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p327_23 : ‖exp (-((((((21327:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6237700072872):ℝ):ℂ) + ((0.7816079439174:ℝ):ℂ) * I)‖ ≤ 0.00000015804 := by
  have hl := lg_23
  refine (ecis_approx ((((21327:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.870685120945508682 66.870685163599572663 2.2443532 0.00000005803 (-0.6237700072872) 0.7816079439174 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p327_24 : ‖exp (-((((((21327:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2319793271513:ℝ):ℂ) + ((0.9727207162256:ℝ):ℂ) * I)‖ ≤ 0.00000016134 := by
  have hl := lg_24
  refine (ecis_approx ((((21327:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.778354017655213628 67.778354060309234955 1.3366843 0.00000006133 0.2319793271513 0.9727207162256 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p327_25 : ‖exp (-((((((21327:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8933395789245:ℝ):ℂ) + ((0.4493822389982:ℝ):ℂ) * I)‖ ≤ 0.00000015848 := by
  have hl := lg_25
  refine (ecis_approx ((((21327:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.648964694788670686 68.64896473744271334 0.4660737 0.00000005847 0.8933395789245 0.4493822389982 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p327_26 : ‖exp (-((((((21327:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9321875116085:ℝ):ℂ) + (((-0.3619757494656):ℝ):ℂ) * I)‖ ≤ 0.00000013478 := by
  have hl := lg_26
  refine (ecis_approx ((((21327:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.4854248442087159 69.485424886862758554 (-0.3703865) 0.00000003477 0.9321875116085 (-0.3619757494656) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p327_27 : ‖exp (-((((((21327:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.385289780733:ℝ):ℂ) + (((-0.922795635481):ℝ):ℂ) * I)‖ ≤ 0.00000015435 := by
  have hl := lg_27
  refine (ecis_approx ((((21327:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.290312824642740884 70.290312856633304865 (-1.1752745) 0.00000005434 0.385289780733 (-0.922795635481) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p327_28 : ‖exp (-((((((21327:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3710048586134):ℝ):ℂ) + (((-0.9286309250087):ℝ):ℂ) * I)‖ ≤ 0.00000013002 := by
  have hl := lg_28
  refine (ecis_approx ((((21327:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.065925566331144994 71.065925608985187648 (-1.9508872) 0.00000003001 (-0.3710048586134) (-0.9286309250087) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p327_29 : ‖exp (-((((((21327:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9037641085522):ℝ):ℂ) + (((-0.4280308820307):ℝ):ℂ) * I)‖ ≤ 0.00000013504 := by
  have hl := lg_29
  refine (ecis_approx ((((21327:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.814318143946100284 71.814318186600164265 (-2.6992798) 0.00000003503 (-0.9037641085522) (-0.4280308820307) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p327_30 : ‖exp (-((((((21327:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9608602153095):ℝ):ℂ) + ((0.2770336557159:ℝ):ℂ) * I)‖ ≤ 0.00000014964 := by
  have hl := lg_30
  refine (ecis_approx ((((21327:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 72.537336536533348971 72.537336579187391625 2.8608871 0.00000004963 (-0.9608602153095) 0.2770336557159 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p327_31 : ‖exp (-((((((21327:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5570108752414):ℝ):ℂ) + ((0.8305051985712:ℝ):ℂ) * I)‖ ≤ 0.00000014439 := by
  have hl := lg_31
  refine (ecis_approx ((((21327:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.236645087879256701 73.236645130533320682 2.1615786 0.00000004438 (-0.5570108752414) 0.8305051985712 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p327_32 : ‖exp (-((((((21327:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0862150613317:ℝ):ℂ) + ((0.9962765495581:ℝ):ℂ) * I)‖ ≤ 0.00000013847 := by
  have hl := lg_32
  refine (ecis_approx ((((21327:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.9137495712905 73.913749624608 1.4844741 0.00000003846 0.0862150613317 0.9962765495581 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p327_33 : ‖exp (-((((((21327:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6761978591712:ℝ):ℂ) + ((0.7367200657321:ℝ):ℂ) * I)‖ ≤ 0.00000014495 := by
  have hl := lg_33
  refine (ecis_approx ((((21327:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.570016741220166919 74.5700167838742309 0.8282069 0.00000004494 0.6761978591712 0.7367200657321 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p327_34 : ‖exp (-((((((21327:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.981713598719:ℝ):ℂ) + ((0.190363888619:ℝ):ℂ) * I)‖ ≤ 0.00000014795 := by
  have hl := lg_34
  refine (ecis_approx ((((21327:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.206690880769587918 75.206690934087109245 0.1915328 0.00000004794 0.981713598719 0.190363888619 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p327_35 : ‖exp (-((((((21327:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9103429277569:ℝ):ℂ) + (((-0.4138547497408):ℝ):ℂ) * I)‖ ≤ 0.00000014172 := by
  have hl := lg_35
  refine (ecis_approx ((((21327:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.824908085209280337 75.824908127863344318 (-0.4266844) 0.00000004171 0.9103429277569 (-0.4138547497408) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p327_36 : ‖exp (-((((((21327:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5169735782836:ℝ):ℂ) + (((-0.8560013547633):ℝ):ℂ) * I)‖ ≤ 0.00000013479 := by
  have hl := lg_36
  refine (ecis_approx ((((21327:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.425708378278027256 76.42570842093206991 (-1.0274847) 0.00000003478 0.5169735782836 (-0.8560013547633) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p327_37 : ‖exp (-((((((21327:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0410147652436):ℝ):ℂ) + (((-0.9991585404888):ℝ):ℂ) * I)‖ ≤ 0.0000001573 := by
  have hl := lg_37
  refine (ecis_approx ((((21327:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.010046300787934534 77.010046343441998515 (-1.6118226) 0.00000005729 (-0.0410147652436) (-0.9991585404888) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p327_38 : ‖exp (-((((((21327:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5726871017082):ℝ):ℂ) + (((-0.8197740441896):ℝ):ℂ) * I)‖ ≤ 0.00000016282 := by
  have hl := lg_38
  refine (ecis_approx ((((21327:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.578800006309182181 77.578800048963246162 (-2.1805763) 0.00000006281 (-0.5726871017082) (-0.8197740441896) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p327_39 : ‖exp (-((((((21327:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9182978138103):ℝ):ℂ) + (((-0.395890294161):ℝ):ℂ) * I)‖ ≤ 0.00000016135 := by
  have hl := lg_39
  refine (ecis_approx ((((21327:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 78.132779204831529528 78.132779247485593509 (-2.7345555) 0.00000006134 (-0.9182978138103) (-0.395890294161) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p327_40 : ‖exp (-((((((21327:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9911796979108):ℝ):ℂ) + ((0.1325247374233:ℝ):ℂ) * I)‖ ≤ 0.00000015017 := by
  have hl := lg_40
  refine (ecis_approx ((((21327:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 78.672732090168635343 78.67273214348615667 3.0086769 0.00000005016 (-0.9911796979108) 0.1325247374233 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p382_2 : ‖exp (-((((((21382:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6316704406139):ℝ):ℂ) + (((-0.7752370311329):ℝ):ℂ) * I)‖ ≤ 0.00000010552 := by
  have hl := lg_2
  refine (ecis_approx ((((21382:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.8208730091746 14.8208730198656 (-2.2545024) 0.00000000551 (-0.6316704406139) (-0.7752370311329) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p382_3 : ‖exp (-((((((21382:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0713562796866):ℝ):ℂ) + ((0.9974508916979:ℝ):ℂ) * I)‖ ≤ 0.00000013273 := by
  have hl := lg_3
  refine (ecis_approx ((((21382:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.490527950743362648 23.49052796143438403 1.6422133 0.00000003272 (-0.0713562796866) 0.9974508916979 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p382_4 : ‖exp (-((((((21382:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2019849018743):ℝ):ℂ) + ((0.9793886355344:ℝ):ℂ) * I)‖ ≤ 0.00000011756 := by
  have hl := lg_4
  refine (ecis_approx ((((21382:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.6417460183492 29.6417460397312 1.7741805 0.00000001755 (-0.2019849018743) 0.9793886355344 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p382_5 : ‖exp (-((((((21382:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9895754715897):ℝ):ℂ) + (((-0.1440152270626):ℝ):ℂ) * I)‖ ≤ 0.00000011805 := by
  have hl := lg_5
  refine (ecis_approx ((((21382:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.413001432549616838 34.41300145393163822 (-2.9970749) 0.00000001804 (-0.9895754715897) (-0.1440152270626) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p382_6 : ‖exp (-((((((21382:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8183345206196:ℝ):ℂ) + (((-0.5747422138335):ℝ):ℂ) * I)‖ ≤ 0.00000013824 := by
  have hl := lg_6
  refine (ecis_approx ((((21382:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.311400959917962648 38.31140098129998403 (-0.6122891) 0.00000003823 0.8183345206196 (-0.5747422138335) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p382_7 : ‖exp (-((((((21382:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7201718435558):ℝ):ℂ) + ((0.6937957305447:ℝ):ℂ) * I)‖ ≤ 0.00000015429 := by
  have hl := lg_7
  refine (ecis_approx ((((21382:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.607450795984393204 41.607450817366435968 2.3748463 0.00000005428 (-0.7201718435558) 0.6937957305447 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p382_8 : ‖exp (-((((((21382:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8868462301102:ℝ):ℂ) + (((-0.4620646752775):ℝ):ℂ) * I)‖ ≤ 0.00000012275 := by
  have hl := lg_8
  refine (ecis_approx ((((21382:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.4626190275238 44.4626190595968 (-0.4803219) 0.00000002274 0.8868462301102 (-0.4620646752775) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p382_9 : ‖exp (-((((((21382:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.989816575735):ℝ):ℂ) + (((-0.1423486775332):ℝ):ℂ) * I)‖ ≤ 0.00000014879 := by
  have hl := lg_9
  refine (ecis_approx ((((21382:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.981055901486725296 46.98105592286876806 (-2.9987588) 0.00000004878 (-0.989816575735) (-0.1423486775332) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p382_10 : ‖exp (-((((((21382:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5134396432153:ℝ):ℂ) + ((0.8581257091912:ℝ):ℂ) * I)‖ ≤ 0.00000011638 := by
  have hl := lg_10
  refine (ecis_approx ((((21382:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.233874441724216838 49.23387447379723822 1.031608 0.00000001637 0.5134396432153 0.8581257091912 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p382_11 : ‖exp (-((((((21382:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5349782699414:ℝ):ℂ) + (((-0.8448658181573):ℝ):ℂ) * I)‖ ≤ 0.00000015115 := by
  have hl := lg_11
  refine (ecis_approx ((((21382:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.271796706300272606 51.27179673837331537 (-1.0063143) 0.00000005114 0.5349782699414 (-0.8448658181573) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p382_12 : ‖exp (-((((((21382:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9624791746436):ℝ):ℂ) + (((-0.2713555566699):ℝ):ℂ) * I)‖ ≤ 0.00000014374 := by
  have hl := lg_12
  refine (ecis_approx ((((21382:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 53.132273969092562648 53.13227400116558403 (-2.8667915) 0.00000004373 (-0.9624791746436) (-0.2713555566699) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p382_13 : ‖exp (-((((((21382:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.133722500663):ℝ):ℂ) + ((0.9910188155711:ℝ):ℂ) * I)‖ ≤ 0.00000012006 := by
  have hl := lg_13
  refine (ecis_approx ((((21382:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.8437471445681094 54.843747176641152164 1.7049206 0.00000002005 (-0.133722500663) 0.9910188155711 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p382_14 : ‖exp (-((((((21382:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9927674081182:ℝ):ℂ) + ((0.120053627093:ℝ):ℂ) * I)‖ ≤ 0.00000015947 := by
  have hl := lg_14
  refine (ecis_approx ((((21382:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 56.428323805158993204 56.428323837232035968 0.1203439 0.00000005946 0.9927674081182 0.120053627093 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p382_15 : ‖exp (-((((((21382:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2142605409791:ℝ):ℂ) + (((-0.976776545879):ℝ):ℂ) * I)‖ ≤ 0.00000015076 := by
  have hl := lg_15
  refine (ecis_approx ((((21382:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.903529383292979486 57.90352941536602225 (-1.3548616) 0.00000005075 0.2142605409791 (-0.976776545879) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p382_16 : ‖exp (-((((((21382:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9184041959449):ℝ):ℂ) + (((-0.3956434414093):ℝ):ℂ) * I)‖ ≤ 0.00000012793 := by
  have hl := lg_16
  refine (ecis_approx ((((21382:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 59.2834920366984 59.2834920794624 (-2.7348243) 0.00000002792 (-0.9184041959449) (-0.3956434414093) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p382_17 : ‖exp (-((((((21382:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6297948494606):ℝ):ℂ) + ((0.7767615126783:ℝ):ℂ) * I)‖ ≤ 0.00000017136 := by
  have hl := lg_17
  refine (ecis_approx ((((21382:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.579767700377391788 60.57976774314141317 2.2520854 0.00000007135 (-0.6297948494606) 0.7767615126783 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p382_18 : ‖exp (-((((((21382:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5148839124803:ℝ):ℂ) + ((0.8572599119689:ℝ):ℂ) * I)‖ ≤ 0.00000016115 := by
  have hl := lg_18
  refine (ecis_approx ((((21382:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.801928910661325296 61.80192894273436806 1.0299241 0.00000006114 0.5148839124803 0.8572599119689 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p382_19 : ‖exp (-((((((21382:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9920547423665:ℝ):ℂ) + (((-0.125806947933):ℝ):ℂ) * I)‖ ≤ 0.00000013595 := by
  have hl := lg_19
  refine (ecis_approx ((((21382:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.957994235862345346 62.957994267935409492 (-0.1261412) 0.00000003594 0.9920547423665 (-0.125806947933) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p382_20 : ‖exp (-((((((21382:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3409261814804:ℝ):ℂ) + (((-0.9400900695046):ℝ):ℂ) * I)‖ ≤ 0.00000012188 := by
  have hl := lg_20
  refine (ecis_approx ((((21382:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.054747450898816838 64.05474749366283822 (-1.2228944) 0.00000002187 0.3409261814804 (-0.9400900695046) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p382_21 : ‖exp (-((((((21382:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6406383810978):ℝ):ℂ) + (((-0.7678427343204):ℝ):ℂ) * I)‖ ≤ 0.00000012508 := by
  have hl := lg_21
  refine (ecis_approx ((((21382:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.097978746727755852 65.097978778800819998 (-2.2661257) 0.00000002507 (-0.6406383810978) (-0.7678427343204) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p382_22 : ‖exp (-((((((21382:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9929012270229):ℝ):ℂ) + ((0.1189418048198:ℝ):ℂ) * I)‖ ≤ 0.00000016352 := by
  have hl := lg_22
  refine (ecis_approx ((((21382:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.092669715474872606 66.09266975823891537 3.0223686 0.00000006351 (-0.9929012270229) 0.1189418048198 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p382_23 : ‖exp (-((((((21382:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4803947755314):ℝ):ℂ) + ((0.8770523699509:ℝ):ℂ) * I)‖ ≤ 0.00000016657 := by
  have hl := lg_23
  refine (ecis_approx ((((21382:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.043137302764423812 67.043137345528487958 2.0719011 0.00000006656 (-0.4803947755314) 0.8770523699509 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p382_24 : ‖exp (-((((((21382:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.397604774743:ℝ):ℂ) + ((0.9175567792249:ℝ):ℂ) * I)‖ ≤ 0.00000014207 := by
  have hl := lg_24
  refine (ecis_approx ((((21382:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.953146978267162648 67.95314702103118403 1.1618914 0.00000004206 0.397604774743 0.9175567792249 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p382_25 : ‖exp (-((((((21382:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.958519230683:ℝ):ℂ) + ((0.2850278660252:ℝ):ℂ) * I)‖ ≤ 0.0000001289 := by
  have hl := lg_25
  refine (ecis_approx ((((21382:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.826002865099233676 68.82600290786327644 0.2890355 0.00000002889 0.958519230683 0.2850278660252 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p382_26 : ‖exp (-((((((21382:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8527430353027:ℝ):ℂ) + (((-0.5223306574792):ℝ):ℂ) * I)‖ ≤ 0.00000012525 := by
  have hl := lg_26
  refine (ecis_approx ((((21382:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.6646201537427094 69.664620196506752164 (-0.5495818) 0.00000002524 0.8527430353027 (-0.5223306574792) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p382_27 : ‖exp (-((((((21382:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2126154439609:ℝ):ℂ) + (((-0.9771359541994):ℝ):ℂ) * I)‖ ≤ 0.00000012676 := by
  have hl := lg_27
  refine (ecis_approx ((((21382:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.471583852230087944 70.47158388430315209 (-1.3565455) 0.00000002675 0.2126154439609 (-0.9771359541994) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p382_28 : ‖exp (-((((((21382:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5340318086688):ℝ):ℂ) + (((-0.8454643856024):ℝ):ℂ) * I)‖ ≤ 0.00000016466 := by
  have hl := lg_28
  refine (ecis_approx ((((21382:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.249196814333593204 71.249196857097635968 (-2.1341585) 0.00000006465 (-0.5340318086688) (-0.8454643856024) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p382_29 : ‖exp (-((((((21382:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9671285090474):ℝ):ℂ) + (((-0.2542881175524):ℝ):ℂ) * I)‖ ≤ 0.00000016445 := by
  have hl := lg_29
  refine (ecis_approx ((((21382:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.999519414538168344 71.99951945730223249 (-2.8844811) 0.00000006444 (-0.9671285090474) (-0.2542881175524) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p382_30 : ‖exp (-((((((21382:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8925753965743):ℝ):ℂ) + ((0.4508981717883:ℝ):ℂ) * I)‖ ≤ 0.00000014909 := by
  have hl := lg_30
  refine (ecis_approx ((((21382:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 72.724402392467579486 72.72440243523162225 2.6738213 0.00000004908 (-0.8925753965743) 0.4508981717883 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p382_31 : ‖exp (-((((((21382:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3911795937044):ℝ):ℂ) + ((0.9203143623057:ℝ):ℂ) * I)‖ ≤ 0.00000014069 := by
  have hl := lg_31
  refine (ecis_approx ((((21382:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.425514384068751666 73.425514426832815812 1.9727093 0.00000004068 (-0.3911795937044) 0.9203143623057 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p382_32 : ‖exp (-((((((21382:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2734113430825:ℝ):ℂ) + ((0.9618972073324:ℝ):ℂ) * I)‖ ≤ 0.0000001403 := by
  have hl := lg_32
  refine (ecis_approx ((((21382:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.104365045873 74.104365099328 1.2938586 0.00000004029 0.2734113430825 0.9618972073324 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p382_33 : ‖exp (-((((((21382:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.80453810463:ℝ):ℂ) + ((0.5939010340101:ℝ):ℂ) * I)‖ ≤ 0.00000012913 := by
  have hl := lg_33
  refine (ecis_approx ((((21382:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.762324657043635254 74.7623246998076994 0.635899 0.00000002912 0.80453810463 0.5939010340101 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p382_34 : ‖exp (-((((((21382:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9999970788152:ℝ):ℂ) + (((-0.0024170976464):ℝ):ℂ) * I)‖ ≤ 0.00000017662 := by
  have hl := lg_34
  refine (ecis_approx ((((21382:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.400640709551991788 75.40064076300701317 (-0.0024171) 0.00000007661 0.9999970788152 (-0.0024170976464) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p382_35 : ‖exp (-((((((21382:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8125815416485:ℝ):ℂ) + (((-0.5828475256635):ℝ):ℂ) * I)‖ ≤ 0.00000015764 := by
  have hl := lg_35
  refine (ecis_approx ((((21382:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.020452228534010042 76.020452271298074188 (-0.6222286) 0.00000005763 0.8125815416485 (-0.5828475256635) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p382_36 : ‖exp (-((((((21382:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3393426812092:ℝ):ℂ) + (((-0.9406628220089):ℝ):ℂ) * I)‖ ≤ 0.00000016633 := by
  have hl := lg_36
  refine (ecis_approx ((((21382:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.622801919835925296 76.62280196259996806 (-1.2245783) 0.00000006632 0.3393426812092 (-0.9406628220089) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p382_37 : ‖exp (-((((((21382:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2373400805208):ℝ):ℂ) + (((-0.9714266241859):ℝ):ℂ) * I)‖ ≤ 0.00000014255 := by
  have hl := lg_37
  refine (ecis_approx ((((21382:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.208646785926178844 77.20864682869024299 (-1.8104231) 0.00000004254 (-0.2373400805208) (-0.9714266241859) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p382_38 : ‖exp (-((((((21382:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7241818610334):ℝ):ℂ) + (((-0.6896090429527):ℝ):ℂ) * I)‖ ≤ 0.00000014113 := by
  have hl := lg_38
  refine (ecis_approx ((((21382:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.778867245036945346 77.778867287801009492 (-2.3806436) 0.00000004112 (-0.7241818610334) (-0.6896090429527) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p382_39 : ‖exp (-((((((21382:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9789506595287):ℝ):ℂ) + (((-0.2040970501757):ℝ):ℂ) * I)‖ ≤ 0.00000015194 := by
  have hl := lg_39
  refine (ecis_approx ((((21382:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 78.334275095311472048 78.334275138075536194 (-2.9360514) 0.00000005193 (-0.9789506595287) (-0.2040970501757) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p382_40 : ‖exp (-((((((21382:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9441456233298):ℝ):ℂ) + ((0.3295285143329:ℝ):ℂ) * I)‖ ≤ 0.00000013328 := by
  have hl := lg_40
  refine (ecis_approx ((((21382:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 78.875620460073416838 78.87562051352843822 2.8057885 0.00000003327 (-0.9441456233298) 0.3295285143329 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p456_2 : ‖exp (-((((((21456:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6705863939273):ℝ):ℂ) + (((-0.7418314419464):ℝ):ℂ) * I)‖ ≤ 0.00000011386 := by
  have hl := lg_2
  refine (ecis_approx ((((21456:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.8721659005168 14.8721659112448 (-2.3057953) 0.00000001385 (-0.6705863939273) (-0.7418314419464) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p456_3 : ‖exp (-((((((21456:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0098801660413:ℝ):ℂ) + ((0.9999511899682:ℝ):ℂ) * I)‖ ≤ 0.00000014211 := by
  have hl := lg_3
  refine (ecis_approx ((((21456:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.571825260085566784 23.57182527081358824 1.560916 0.0000000421 0.0098801660413 0.9999511899682 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p456_4 : ‖exp (-((((((21456:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1006277694101):ℝ):ℂ) + ((0.9949241438537:ℝ):ℂ) * I)‖ ≤ 0.00000013488 := by
  have hl := lg_4
  refine (ecis_approx ((((21456:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.7443318010336 29.7443318224896 1.6715947 0.00000003487 (-0.1006277694101) 0.9949241438537 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p456_5 : ‖exp (-((((((21456:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9996769453206):ℝ):ℂ) + (((-0.0254166159707):ℝ):ℂ) * I)‖ ≤ 0.0000001236 := by
  have hl := lg_5
  refine (ecis_approx ((((21456:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.532099838031268304 34.53209985948728976 (-3.1161733) 0.00000002359 (-0.9996769453206) (-0.0254166159707) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p456_6 : ‖exp (-((((((21456:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7351697282241:ℝ):ℂ) + (((-0.6778830804076):ℝ):ℂ) * I)‖ ≤ 0.000000139 := by
  have hl := lg_6
  refine (ecis_approx ((((21456:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.443991160602366784 38.44399118205838824 (-0.7448793) 0.00000003899 0.7351697282241 (-0.6778830804076) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p456_7 : ‖exp (-((((((21456:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6131584625446):ℝ):ℂ) + ((0.7899599355643:ℝ):ℂ) * I)‖ ≤ 0.00000011819 := by
  have hl := lg_7
  refine (ecis_approx ((((21456:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.751448146976014432 41.751448168432057344 2.230849 0.00000001818 (-0.6131584625446) 0.7899599355643 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p456_8 : ‖exp (-((((((21456:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8055456252913:ℝ):ℂ) + (((-0.592533750578):ℝ):ℂ) * I)‖ ≤ 0.00000014872 := by
  have hl := lg_8
  refine (ecis_approx ((((21456:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.6164977015504 44.6164977337344 (-0.6342006) 0.00000004871 0.8055456252913 (-0.592533750578) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p456_9 : ‖exp (-((((((21456:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9998047623476):ℝ):ℂ) + ((0.0197594672735:ℝ):ℂ) * I)‖ ≤ 0.00000013728 := by
  have hl := lg_9
  refine (ecis_approx ((((21456:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.143650520171133568 47.14365054162717648 3.1218319 0.00000003727 (-0.9998047623476) 0.0197594672735 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p456_10 : ‖exp (-((((((21456:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6515149184245:ℝ):ℂ) + ((0.7586358224275:ℝ):ℂ) * I)‖ ≤ 0.0000001189 := by
  have hl := lg_10
  refine (ecis_approx ((((21456:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.404265738548068304 49.40426577073208976 0.8612167 0.00000001889 0.6515149184245 0.7586358224275 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p456_11 : ‖exp (-((((((21456:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3774470103208:ℝ):ℂ) + (((-0.9260311843561):ℝ):ℂ) * I)‖ ≤ 0.00000013119 := by
  have hl := lg_11
  refine (ecis_approx ((((21456:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.449240956429644048 51.44924098861368696 (-1.1837585) 0.00000003118 0.3774470103208 (-0.9260311843561) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p456_12 : ‖exp (-((((((21456:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9958697997671):ℝ):ℂ) + (((-0.090792848945):ℝ):ℂ) * I)‖ ≤ 0.00000013588 := by
  have hl := lg_12
  refine (ecis_approx ((((21456:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 53.316157061119166784 53.31615709330318824 (-3.0506746) 0.00000003587 (-0.9958697997671) (-0.090792848945) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p456_13 : ‖exp (-((((((21456:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0556531578331:ℝ):ℂ) + ((0.9984501620126:ℝ):ℂ) * I)‖ ≤ 0.00000016455 := by
  have hl := lg_13
  refine (ecis_approx ((((21456:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.0335533969625552 55.033553429146598112 1.5151144 0.00000006454 0.0556531578331 0.9984501620126 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p456_14 : ‖exp (-((((((21456:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9971928403997:ℝ):ℂ) + (((-0.0748761581252):ℝ):ℂ) * I)‖ ≤ 0.00000011714 := by
  have hl := lg_14
  refine (ecis_approx ((((21456:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 56.623614047492814432 56.623614079676857344 (-0.0749463) 0.00000001713 0.9971928403997 (-0.0748761581252) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p456_15 : ‖exp (-((((((21456:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0155384014567:ℝ):ℂ) + (((-0.9998792717523):ℝ):ℂ) * I)‖ ≤ 0.0000001657 := by
  have hl := lg_15
  refine (ecis_approx ((((21456:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.103925098116835088 58.103925130300878 (-1.5552573) 0.00000006569 0.0155384014567 (-0.9998792717523) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p456_16 : ‖exp (-((((((21456:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9797481024775):ℝ):ℂ) + (((-0.2002340015309):ℝ):ℂ) * I)‖ ≤ 0.00000016256 := by
  have hl := lg_16
  refine (ecis_approx ((((21456:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 59.4886636020672 59.4886636449792 (-2.9399959) 0.00000006255 (-0.9797481024775) (-0.2002340015309) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p456_17 : ‖exp (-((((((21456:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4543400736162):ℝ):ℂ) + ((0.8908283210034:ℝ):ℂ) * I)‖ ≤ 0.00000015889 := by
  have hl := lg_17
  refine (ecis_approx ((((21456:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.789425487760607904 60.78942553067262936 2.0424276 0.00000005888 (-0.4543400736162) 0.8908283210034 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p456_18 : ‖exp (-((((((21456:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.68511366474:ℝ):ℂ) + ((0.7284361786639:ℝ):ℂ) * I)‖ ≤ 0.00000015112 := by
  have hl := lg_18
  refine (ecis_approx ((((21456:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.015816420687933568 62.01581645287197648 0.8160366 0.00000005111 0.68511366474 0.7284361786639 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p456_19 : ‖exp (-((((((21456:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9414031617881:ℝ):ℂ) + (((-0.3372833926764):ℝ):ℂ) * I)‖ ≤ 0.00000015155 := by
  have hl := lg_19
  refine (ecis_approx ((((21456:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.175882720262953968 63.175882752447018336 (-0.3440297) 0.00000005154 0.9414031617881 (-0.3372833926764) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p456_20 : ‖exp (-((((((21456:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1258828663343:ℝ):ℂ) + (((-0.992045111859):ℝ):ℂ) * I)‖ ≤ 0.00000013275 := by
  have hl := lg_20
  refine (ecis_approx ((((21456:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.276431639064868304 64.27643168197688976 (-1.4445786) 0.00000003274 0.1258828663343 (-0.992045111859) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p456_21 : ‖exp (-((((((21456:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7959795411986):ℝ):ℂ) + (((-0.6053235250223):ℝ):ℂ) * I)‖ ≤ 0.00000016475 := by
  have hl := lg_21
  refine (ecis_approx ((((21456:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.323273407061581216 65.323273439245645584 (-2.4914204) 0.00000006474 (-0.7959795411986) (-0.6053235250223) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p456_22 : ‖exp (-((((((21456:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9400698758294):ℝ):ℂ) + ((0.3409818593101:ℝ):ℂ) * I)‖ ≤ 0.00000012204 := by
  have hl := lg_22
  refine (ecis_approx ((((21456:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.321406856946444048 66.32140689985848696 2.7936315 0.00000002203 (-0.9400698758294) 0.3409818593101 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p456_23 : ‖exp (-((((((21456:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2658428936489):ℝ):ℂ) + ((0.9640163670265:ℝ):ℂ) * I)‖ ≤ 0.00000013862 := by
  have hl := lg_23
  refine (ecis_approx ((((21456:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.275163874666236896 67.275163917578301264 1.8398745 0.00000003861 (-0.2658428936489) 0.9640163670265 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p456_24 : ‖exp (-((((((21456:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6004637535186:ℝ):ℂ) + ((0.799651974743:ℝ):ℂ) * I)‖ ≤ 0.00000012559 := by
  have hl := lg_24
  refine (ecis_approx ((((21456:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.188322961635966784 68.18832300454798824 0.9267154 0.00000002558 0.6004637535186 0.799651974743 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p456_25 : ‖exp (-((((((21456:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9987079916013:ℝ):ℂ) + ((0.0508168034378:ℝ):ℂ) * I)‖ ≤ 0.00000014001 := by
  have hl := lg_25
  refine (ecis_approx ((((21456:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.064199676062536608 69.06419971897457952 0.0508387 0.00000004 0.9987079916013 0.0508168034378 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p456_26 : ‖exp (-((((((21456:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7033614729864:ℝ):ℂ) + (((-0.7108323559873):ℝ):ℂ) * I)‖ ≤ 0.00000016143 := by
  have hl := lg_26
  refine (ecis_approx ((((21456:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.9057192974793552 69.905719340391398112 (-0.7906809) 0.00000006142 0.7033614729864 (-0.7108323559873) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p456_27 : ‖exp (-((((((21456:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0296367329882):ℝ):ℂ) + (((-0.9995607355521):ℝ):ℂ) * I)‖ ≤ 0.00000013348 := by
  have hl := lg_27
  refine (ecis_approx ((((21456:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.715475780256700352 70.71547581244076472 (-1.6004374) 0.00000003347 (-0.0296367329882) (-0.9995607355521) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p456_28 : ‖exp (-((((((21456:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.724249439242):ℝ):ℂ) + (((-0.6895380698189):ℝ):ℂ) * I)‖ ≤ 0.00000013098 := by
  have hl := lg_28
  refine (ecis_approx ((((21456:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.495779948009614432 71.495779990921657344 (-2.3807416) 0.00000003097 (-0.724249439242) (-0.6895380698189) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p456_29 : ‖exp (-((((((21456:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9999685434757):ℝ):ℂ) + (((-0.0079316701245):ℝ):ℂ) * I)‖ ≤ 0.00000016983 := by
  have hl := lg_29
  refine (ecis_approx ((((21456:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 72.248699305880223552 72.24869934879228792 (-3.1336609) 0.00000006982 (-0.9999685434757) (-0.0079316701245) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p456_30 : ‖exp (-((((((21456:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7521617178107):ℝ):ℂ) + ((0.6589785658318:ℝ):ℂ) * I)‖ ≤ 0.00000015541 := by
  have hl := lg_30
  refine (ecis_approx ((((21456:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 72.976090998633635088 72.976091041545678 2.4221327 0.0000000554 (-0.7521617178107) 0.6589785658318 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p456_31 : ‖exp (-((((((21456:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1472603726091):ℝ):ℂ) + ((0.9890977619318:ℝ):ℂ) * I)‖ ≤ 0.00000014905 := by
  have hl := lg_31
  refine (ecis_approx ((((21456:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.679629437123708528 73.679629480035772896 1.7185942 0.00000004904 (-0.1472603726091) 0.9890977619318 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p456_32 : ‖exp (-((((((21456:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5084657889591:ℝ):ℂ) + ((0.8610821920457:ℝ):ℂ) * I)‖ ≤ 0.00000017008 := by
  have hl := lg_32
  refine (ecis_approx ((((21456:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.360829502584 74.360829556224 1.0373942 0.00000007007 0.5084657889591 0.8610821920457 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p456_33 : ‖exp (-((((((21456:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9297152607063:ℝ):ℂ) + ((0.3682791522878:ℝ):ℂ) * I)‖ ≤ 0.00000016965 := by
  have hl := lg_33
  refine (ecis_approx ((((21456:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.021066216515210832 75.0210662594272752 0.3771574 0.00000006964 0.9297152607063 0.3682791522878 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p456_34 : ‖exp (-((((((21456:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9655187294924:ℝ):ℂ) + (((-0.260333599444):ℝ):ℂ) * I)‖ ≤ 0.00000015578 := by
  have hl := lg_34
  refine (ecis_approx ((((21456:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.661591388277407904 75.66159144191742936 (-0.2633677) 0.00000005577 0.9655187294924 (-0.260333599444) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p456_35 : ‖exp (-((((((21456:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6330384875608:ℝ):ℂ) + (((-0.7741203222153):ℝ):ℂ) * I)‖ ≤ 0.00000014178 := by
  have hl := lg_35
  refine (ecis_approx ((((21456:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.283547985007282736 76.283548027919347104 (-0.8853243) 0.00000004177 0.6330384875608 (-0.7741203222153) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p456_36 : ‖exp (-((((((21456:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0809489589224:ℝ):ℂ) + (((-0.9967182480768):ℝ):ℂ) * I)‖ ≤ 0.00000016497 := by
  have hl := lg_36
  refine (ecis_approx ((((21456:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.887982321204733568 76.88798236411677648 (-1.4897587) 0.00000006496 0.0809489589224 (-0.9967182480768) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p456_37 : ‖exp (-((((((21456:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4854122843272):ℝ):ℂ) + (((-0.8742853734443):ℝ):ℂ) * I)‖ ≤ 0.00000016816 := by
  have hl := lg_37
  refine (ecis_approx ((((21456:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.475854711384907552 77.47585475429697192 (-2.077631) 0.00000006815 (-0.4854122843272) (-0.8742853734443) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p456_38 : ‖exp (-((((((21456:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8814995770079):ℝ):ℂ) + (((-0.4721848108922):ℝ):ℂ) * I)‖ ≤ 0.00000016539 := by
  have hl := lg_38
  refine (ecis_approx ((((21456:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 78.048048620779753968 78.048048663691818336 (-2.649825) 0.00000006538 (-0.8814995770079) (-0.4721848108922) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p456_39 : ‖exp (-((((((21456:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9978515583823):ℝ):ℂ) + ((0.065515394321:ℝ):ℂ) * I)‖ ≤ 0.0000001363 := by
  have hl := lg_39
  refine (ecis_approx ((((21456:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 78.605378657048121984 78.605378699960186352 3.0760303 0.00000003629 (-0.9978515583823) 0.065515394321 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p456_40 : ‖exp (-((((((21456:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8203455890913):ℝ):ℂ) + ((0.5718680917839:ℝ):ℂ) * I)‖ ≤ 0.00000015377 := by
  have hl := lg_40
  refine (ecis_approx ((((21456:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.148597539581668304 79.14859759322168976 2.5328114 0.00000005376 (-0.8203455890913) 0.5718680917839 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p53_2 : ‖exp (-((((((21530:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7077384469752):ℝ):ℂ) + (((-0.7064745506019):ℝ):ℂ) * I)‖ ≤ 0.00000012252 := by
  have hl := lg_2
  refine (ecis_approx ((((21530:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.923458791859 14.923458802624 (-2.3570882) 0.00000002251 (-0.7077384469752) (-0.7064745506019) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p53_3 : ‖exp (-((((((21530:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0910513472297:ℝ):ℂ) + ((0.9958461990526:ℝ):ℂ) * I)‖ ≤ 0.00000015149 := by
  have hl := lg_3
  refine (ecis_approx ((((21530:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.65312256942777092 23.65312258019279245 1.4796187 0.00000005148 0.0910513472297 0.9958461990526 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p53_4 : ‖exp (-((((((21530:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0017874258431:ℝ):ℂ) + ((0.999998402553:ℝ):ℂ) * I)‖ ≤ 0.00000015219 := by
  have hl := lg_4
  refine (ecis_approx ((((21530:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.846917583718 29.846917605248 1.5690089 0.00000005218 0.0017874258431 0.999998402553 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p53_5 : ‖exp (-((((((21530:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9956153252164):ℝ):ℂ) + ((0.0935420959092:ℝ):ℂ) * I)‖ ≤ 0.00000012198 := by
  have hl := lg_5
  refine (ecis_approx ((((21530:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 34.65119824351291977 34.6511982650429413 3.0479136 0.00000002197 (-0.9956153252164) 0.0935420959092 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p53_6 : ‖exp (-((((((21530:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6390994568748:ℝ):ℂ) + (((-0.7691241019643):ℝ):ℂ) * I)‖ ≤ 0.00000013975 := by
  have hl := lg_6
  refine (ecis_approx ((((21530:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.57658136128677092 38.57658138281679245 (-0.8774695) 0.00000003974 0.6390994568748 (-0.7691241019643) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p53_7 : ‖exp (-((((((21530:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4934529712122):ℝ):ℂ) + ((0.8697724789828:ℝ):ℂ) * I)‖ ≤ 0.0000001523 := by
  have hl := lg_7
  refine (ecis_approx ((((21530:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.89544549796763566 41.89544551949767872 2.0868516 0.00000005229 (-0.4934529712122) 0.8697724789828 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p53_8 : ‖exp (-((((((21530:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7052084629703:ℝ):ℂ) + (((-0.7090000167526):ℝ):ℂ) * I)‖ ≤ 0.00000015763 := by
  have hl := lg_8
  refine (ecis_approx ((((21530:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.770376375577 44.770376407872 (-0.7880792) 0.00000005762 0.7052084629703 (-0.7090000167526) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p53_9 : ‖exp (-((((((21530:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9834192860553):ℝ):ℂ) + ((0.1813463742861:ℝ):ℂ) * I)‖ ≤ 0.0000001186 := by
  have hl := lg_9
  refine (ecis_approx ((((21530:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.30624513885554184 47.3062451603855849 2.9592373 0.00000001859 (-0.9834192860553) 0.1813463742861 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p53_10 : ‖exp (-((((((21530:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7707203545473:ℝ):ℂ) + ((0.6371735517788:ℝ):ℂ) * I)‖ ≤ 0.00000012208 := by
  have hl := lg_10
  refine (ecis_approx ((((21530:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.57465703537191977 49.5746570676669413 0.6908254 0.00000002207 0.7707203545473 0.6371735517788 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p53_11 : ‖exp (-((((((21530:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2080623392755:ℝ):ℂ) + (((-0.9781155672901):ℝ):ℂ) * I)‖ ≤ 0.00000015089 := by
  have hl := lg_11
  refine (ecis_approx ((((21530:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.62668520655901549 51.62668523885405855 (-1.3612028) 0.00000005088 0.2080623392755 (-0.9781155672901) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p53_12 : ‖exp (-((((((21530:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9956818604862):ℝ):ℂ) + ((0.092831202783:ℝ):ℂ) * I)‖ ≤ 0.00000012084 := by
  have hl := lg_12
  refine (ecis_approx ((((21530:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 53.50004015314577092 53.50004018544079245 3.0486276 0.00000002083 (-0.9956818604862) 0.092831202783 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p53_13 : ‖exp (-((((((21530:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.243029942898:ℝ):ℂ) + ((0.9700187868567:ℝ):ℂ) * I)‖ ≤ 0.00000011705 := by
  have hl := lg_13
  refine (ecis_approx ((((21530:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.223359649357001 55.22335968165204406 1.3253081 0.00000001704 0.243029942898 0.9700187868567 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p53_14 : ‖exp (-((((((21530:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9637077874288:ℝ):ℂ) + (((-0.2669593610443):ℝ):ℂ) * I)‖ ≤ 0.00000015752 := by
  have hl := lg_14
  refine (ecis_approx ((((21530:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 56.81890428982663566 56.81890432212167872 (-0.2702365) 0.00000005751 0.9637077874288 (-0.2669593610443) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p53_15 : ‖exp (-((((((21530:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1838057488331):ℝ):ℂ) + (((-0.9829625866202):ℝ):ℂ) * I)‖ ≤ 0.00000015169 := by
  have hl := lg_15
  refine (ecis_approx ((((21530:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.30432081294069069 58.30432084523573375 (-1.7556531) 0.00000005168 (-0.1838057488331) (-0.9829625866202) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p53_16 : ‖exp (-((((((21530:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9999936102369):ℝ):ℂ) + ((0.0035747456748:ℝ):ℂ) * I)‖ ≤ 0.00000013872 := by
  have hl := lg_16
  refine (ecis_approx ((((21530:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 59.693835167436 59.693835210496 3.1380179 0.00000003871 (-0.9999936102369) 0.0035747456748 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p53_17 : ‖exp (-((((((21530:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2589871947695):ℝ):ℂ) + ((0.9658807550335:ℝ):ℂ) * I)‖ ≤ 0.00000014642 := by
  have hl := lg_17
  refine (ecis_approx ((((21530:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.99908327514382402 60.99908331820384555 1.8327698 0.00000004641 (-0.2589871947695) 0.9658807550335 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p53_18 : ‖exp (-((((((21530:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8241202367447:ℝ):ℂ) + ((0.5664148968626:ℝ):ℂ) * I)‖ ≤ 0.0000001411 := by
  have hl := lg_18
  refine (ecis_approx ((((21530:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.22970393071454184 62.2297039630095849 0.6021491 0.00000004109 0.8241202367447 0.5664148968626 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p53_19 : ‖exp (-((((((21530:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8462346848211:ℝ):ℂ) + (((-0.5328103398075):ℝ):ℂ) * I)‖ ≤ 0.00000016518 := by
  have hl := lg_19
  refine (ecis_approx ((((21530:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.39377120466356259 63.39377123695862718 (-0.5619181) 0.00000006517 0.8462346848211 (-0.5328103398075) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p53_20 : ‖exp (-((((((21530:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0953215281248):ℝ):ℂ) + (((-0.9954465361211):ℝ):ℂ) * I)‖ ≤ 0.00000014458 := by
  have hl := lg_20
  refine (ecis_approx ((((21530:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.49811582723091977 64.4981158702909413 (-1.6662628) 0.00000004457 (-0.0953215281248) (-0.9954465361211) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p53_21 : ‖exp (-((((((21530:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.911089172063):ℝ):ℂ) + (((-0.4122093162694):ℝ):ℂ) * I)‖ ≤ 0.00000012791 := by
  have hl := lg_21
  refine (ecis_approx ((((21530:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.54856806739540658 65.54856809969047117 (-2.716715) 0.0000000279 (-0.911089172063) (-0.4122093162694) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p53_22 : ‖exp (-((((((21530:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8382675233209):ℝ):ℂ) + ((0.5452591670743:ℝ):ℂ) * I)‖ ≤ 0.00000016252 := by
  have hl := lg_22
  refine (ecis_approx ((((21530:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.55014399841801549 66.55014404147805855 2.5648944 0.00000006251 (-0.8382675233209) 0.5452591670743 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p53_23 : ‖exp (-((((((21530:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0370430962693):ℝ):ℂ) + ((0.9993136689841:ℝ):ℂ) * I)‖ ≤ 0.00000013242 := by
  have hl := lg_23
  refine (ecis_approx ((((21530:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.50719044656804998 67.50719048962811457 1.6078479 0.00000003241 (-0.0370430962693) 0.9993136689841 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p53_24 : ‖exp (-((((((21530:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.770265216215:ℝ):ℂ) + ((0.6377236836509:ℝ):ℂ) * I)‖ ≤ 0.00000013399 := by
  have hl := lg_24
  refine (ecis_approx ((((21530:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.42349894500477092 68.42349898806479245 0.6915394 0.00000003398 0.770265216215 0.6377236836509 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p53_25 : ‖exp (-((((((21530:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9824997538376:ℝ):ℂ) + (((-0.1862638819229):ℝ):ℂ) * I)‖ ≤ 0.00000015113 := by
  have hl := lg_25
  refine (ecis_approx ((((21530:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.30239648702583954 69.3023965300858826 (-0.1873581) 0.00000005112 0.9824997538376 (-0.1862638819229) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p53_26 : ‖exp (-((((((21530:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5132919521778:ℝ):ℂ) + (((-0.8582140594452):ℝ):ℂ) * I)‖ ≤ 0.00000013777 := by
  have hl := lg_26
  refine (ecis_approx ((((21530:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.146818441216001 70.14681848427604406 (-1.0317801) 0.00000003776 0.5132919521778 (-0.8582140594452) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p53_27 : ‖exp (-((((((21530:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2701347417025):ℝ):ℂ) + (((-0.9628225284672):ℝ):ℂ) * I)‖ ≤ 0.00000016162 := by
  have hl := lg_27
  refine (ecis_approx ((((21530:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.95936770828331276 70.95936774057837735 (-1.8443293) 0.00000006161 (-0.2701347417025) (-0.9628225284672) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p53_28 : ‖exp (-((((((21530:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8706530474192):ℝ):ℂ) + (((-0.4918976224087):ℝ):ℂ) * I)‖ ≤ 0.00000014579 := by
  have hl := lg_28
  refine (ecis_approx ((((21530:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.74236308168563566 71.74236312474567872 (-2.6273247) 0.00000004578 (-0.8706530474192) (-0.4918976224087) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p53_29 : ‖exp (-((((((21530:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9710405288171):ℝ):ℂ) + ((0.2389148197965:ℝ):ℂ) * I)‖ ≤ 0.00000015414 := by
  have hl := lg_29
  refine (ecis_approx ((((21530:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 72.49787919722227876 72.49787924028234335 2.9003445 0.00000005413 (-0.9710405288171) 0.2389148197965 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p53_30 : ‖exp (-((((((21530:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5643517330563):ℝ):ℂ) + ((0.8255344459117:ℝ):ℂ) * I)‖ ≤ 0.00000016172 := by
  have hl := lg_30
  refine (ecis_approx ((((21530:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.22777960479969069 73.22777964785973375 2.1704441 0.00000006171 (-0.5643517330563) 0.8255344459117 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p604_2 : ‖exp (-((((((21604:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7430288755614):ℝ):ℂ) + (((-0.6692593593293):ℝ):ℂ) * I)‖ ≤ 0.00000013117 := by
  have hl := lg_2
  refine (ecis_approx ((((21604:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.9747516832012 14.9747516940032 (-2.4083811) 0.00000003116 (-0.7430288755614) (-0.6692593593293) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p604_3 : ‖exp (-((((((21604:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1716211770985:ℝ):ℂ) + ((0.9851630177647:ℝ):ℂ) * I)‖ ≤ 0.00000014996 := by
  have hl := lg_3
  refine (ecis_approx ((((21604:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.734419878769975056 23.73441988957199666 1.3983213 0.00000004995 0.1716211770985 0.9851630177647 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p604_4 : ‖exp (-((((((21604:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1041837275364:ℝ):ℂ) + ((0.9945580681471:ℝ):ℂ) * I)‖ ≤ 0.00000015212 := by
  have hl := lg_4
  refine (ecis_approx ((((21604:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.9495033664024 29.9495033880064 1.4664232 0.00000005211 0.1041837275364 0.9945580681471 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p604_5 : ‖exp (-((((((21604:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9774481552623):ℝ):ℂ) + ((0.2111755276197:ℝ):ℂ) * I)‖ ≤ 0.00000012754 := by
  have hl := lg_5
  refine (ecis_approx ((((21604:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 34.770296648994571236 34.77029667059859284 2.9288152 0.00000002753 (-0.9774481552623) 0.2111755276197 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p604_6 : ‖exp (-((((((21604:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5318101645655:ℝ):ℂ) + (((-0.846863595194):ℝ):ℂ) * I)‖ ≤ 0.00000014051 := by
  have hl := lg_6
  refine (ecis_approx ((((21604:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.709171561971175056 38.70917158357519666 (-1.0100597) 0.0000000405 0.5318101645655 (-0.846863595194) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p604_7 : ‖exp (-((((((21604:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3635333695401):ℝ):ℂ) + ((0.9315811769396:ℝ):ℂ) * I)‖ ≤ 0.00000012032 := by
  have hl := lg_7
  refine (ecis_approx ((((21604:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.039442848959256888 42.039442870563300096 1.9428543 0.00000002031 (-0.3635333695401) 0.9315811769396 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p604_8 : ‖exp (-((((((21604:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5882057775983:ℝ):ℂ) + (((-0.8087112978066):ℝ):ℂ) * I)‖ ≤ 0.00000013177 := by
  have hl := lg_8
  refine (ecis_approx ((((21604:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.9242550496036 44.9242550820096 (-0.9419579) 0.00000003176 0.5882057775983 (-0.8087112978066) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p604_9 : ‖exp (-((((((21604:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9410923768952):ℝ):ℂ) + ((0.338149579281:ℝ):ℂ) * I)‖ ≤ 0.00000012172 := by
  have hl := lg_9
  refine (ecis_approx ((((21604:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.468839757539950112 47.46883977914399332 2.7966427 0.00000002171 (-0.9410923768952) 0.338149579281 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p604_10 : ‖exp (-((((((21604:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8676034022494:ℝ):ℂ) + ((0.4972568113211:ℝ):ℂ) * I)‖ ≤ 0.00000012526 := by
  have hl := lg_10
  refine (ecis_approx ((((21604:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.745048332195771236 49.74504836460179284 0.5204341 0.00000002525 0.8676034022494 0.4972568113211 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p604_11 : ‖exp (-((((((21604:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0321437889351:ℝ):ℂ) + (((-0.9994832549036):ℝ):ℂ) * I)‖ ≤ 0.00000013167 := by
  have hl := lg_11
  refine (ecis_approx ((((21604:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.804129456688386932 51.80412948909443014 (-1.538647) 0.00000003166 0.0321437889351 (-0.9994832549036) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

end H22
end Cert
end ZB
end RHV6Fresh
