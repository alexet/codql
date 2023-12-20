import lib
import range

module Impl<inStr/0 input> {
  import Helpers<input/0>

  string instr(int n) { result = groupedLines(0, n) }

  string key(int n) { result = instr(n).splitAt("{", 0) }

  string instruction(string key, int x) {
    exists(int n |
      key = key(n) and
      result = instr(n).splitAt("{", 1).splitAt("}", 0).splitAt(",", x)
    )
  }

  string directInstruction(string key, int x) {
    result = instruction(key, x) and result.regexpMatch("(A|R|[a-z]+)")
  }

  string comparisonParts(string key, int x, int k) {
    result = instruction(key, x).regexpCapture("([xmas])(<|>)([0-9]+):(A|R|[a-z]+)", k)
  }

  predicate isComparison(string key, int x, string lhs, string op, int rhs, string ifTrue) {
    comparisonParts(key, x, 1) = lhs and
    comparisonParts(key, x, 2) = op and
    comparisonParts(key, x, 3).toInt() = rhs and
    comparisonParts(key, x, 4) = ifTrue
  }

  string input(int k) { result = groupedLines(1, k) }

  string input(int k, int x, int part) {
    result = input(k).splitAt("{", 1).splitAt("}", 0).splitAt(",", x).splitAt("=", part)
  }

  int initialValue(int k, string name) {
    exists(int x |
      result = input(k, x, 1).toInt() and
      name = input(k, x, 0)
    )
  }

  predicate intialState(int k, int x, int m, int a, int s) {
    initialValue(k, "x") = x and
    initialValue(k, "m") = m and
    initialValue(k, "a") = a and
    initialValue(k, "s") = s
  }

  predicate reachesState(int k, int x, int m, int a, int s, string key, int instr) {
    intialState(k, x, m, a, s) and key = "in" and instr = 0
    or
    exists(int prevInstr, string prevKey |
      reachesState(k, x, m, a, s, prevKey, prevInstr) and
      (
        key = directInstruction(prevKey, prevInstr) and instr = 0
        or
        exists(string lhs, string op, int rhs, string target |
          isComparison(prevKey, prevInstr, lhs, op, rhs, target)
        |
          exists(int lhsValue |
            lhs = "x" and lhsValue = x
            or
            lhs = "m" and lhsValue = m
            or
            lhs = "a" and lhsValue = a
            or
            lhs = "s" and lhsValue = s
          |
            (
              op = "<" and lhsValue < rhs
              or
              op = ">" and lhsValue > rhs
            ) and
            key = target and
            instr = 0
            or
            (
              op = "<" and lhsValue >= rhs
              or
              op = ">" and lhsValue <= rhs
            ) and
            key = prevKey and
            instr = prevInstr + 1
          )
        )
      )
    )
  }

  predicate accepted(int k) { reachesState(k, _, _, _, _, "A", _) }

  int rating(int k) {
    exists(int x, int m, int a, int s |
      intialState(k, x, m, a, s) and
      result = x + m + a + s
    )
  }

  int score() { result = sum(int k | accepted(k) | rating(k)) }

  predicate acceptsRange(
    string state, int instr, int minX, int maxX, int minM, int maxM, int minA, int maxA, int minS,
    int maxS
  ) {
    state = "A" and
    instr = 0 and
    minX = 1 and
    maxX = 4000 and
    minM = 1 and
    maxM = 4000 and
    minA = 1 and
    maxA = 4000 and
    minS = 1 and
    maxS = 4000
    or
    exists(string next |
      directInstruction(state, instr) = next and
      acceptsRange(next, 0, minX, maxX, minM, maxM, minA, maxA, minS, maxS)
    )
    or
    exists(
      string lhs, string op, int rhs, string target, int rangeLower, int rangeUpper, string next,
      int nextInstr
    |
      isComparison(state, instr, lhs, op, rhs, target) and
      (
        next = target and
        nextInstr = 0 and
        (
          op = "<" and rangeLower = 1 and rangeUpper = rhs - 1
          or
          op = ">" and rangeLower = rhs + 1 and rangeUpper = 4000
        )
        or
        next = state and
        nextInstr = instr + 1 and
        (
          op = "<" and rangeLower = rhs and rangeUpper = 4000
          or
          op = ">" and rangeLower = 1 and rangeUpper = rhs
        )
      )
    |
      lhs = "x" and
      exists(int prevMinX, int prevMaxX |
        acceptsRange(next, nextInstr, prevMinX, prevMaxX, minM, maxM, minA, maxA, minS, maxS) and
        intersectRange(prevMinX, prevMaxX, rangeLower, rangeUpper, minX, maxX)
      )
      or
      lhs = "m" and
      exists(int prevMinM, int prevMaxM |
        acceptsRange(next, nextInstr, minX, maxX, prevMinM, prevMaxM, minA, maxA, minS, maxS) and
        intersectRange(prevMinM, prevMaxM, rangeLower, rangeUpper, minM, maxM)
      )
      or
      lhs = "a" and
      exists(int prevMinA, int prevMaxA |
        acceptsRange(next, nextInstr, minX, maxX, minM, maxM, prevMinA, prevMaxA, minS, maxS) and
        intersectRange(prevMinA, prevMaxA, rangeLower, rangeUpper, minA, maxA)
      )
      or
      lhs = "s" and
      exists(int prevMinS, int prevMaxS |
        acceptsRange(next, nextInstr, minX, maxX, minM, maxM, minA, maxA, prevMinS, prevMaxS) and
        intersectRange(prevMinS, prevMaxS, rangeLower, rangeUpper, minS, maxS)
      )
    )
  }

  predicate startRange(
    int minX, int maxX, int minM, int maxM, int minA, int maxA, int minS, int maxS
  ) {
    acceptsRange("in", 0, minX, maxX, minM, maxM, minA, maxA, minS, maxS)
  }

  string rangeStrings(
    int minX, int maxX, int minM, int maxM, int minA, int maxA, int minS, int maxS
  ) {
    result =
      "x=" + minX + ".." + maxX + ",m=" + minM + ".." + maxM + ",a=" + minA + ".." + maxA + ",s=" +
        minS + ".." + maxS and
    startRange(minX, maxX, minM, maxM, minA, maxA, minS, maxS)
  }

  float scoreP2() {
    result = sum(int minX, int maxX, int minM, int maxM, int minA, int maxA, int minS, int maxS |
      startRange(minX, maxX, minM, maxM, minA, maxA, minS, maxS) |
      (maxX - minX + 1).(float) * (maxM - minM + 1).(float) * (maxA - minA + 1).(float) * (maxS - minS + 1).(float)
    )
  }


  predicate hasIntersection(string source1, string source2) {
    source1 != source2 and
    exists (int minX1, int minX2, int maxX1, int maxX2, int minM1, int minM2, int maxM1, int maxM2,
      int minA1, int minA2, int maxA1, int maxA2, int minS1, int minS2, int maxS1, int maxS2 |
      source1 = rangeStrings(minX1, maxX1, minM1, maxM1, minA1, maxA1, minS1, maxS1) and
      source2 = rangeStrings(minX2, maxX2, minM2, maxM2, minA2, maxA2, minS2, maxS2) and
      intersectRange(minX1, maxX1 + 1, minX2, maxX2 + 1, _, _) and
      intersectRange(minM1, maxM1 + 1, minM2, maxM2 + 1, _, _) and
      intersectRange(minA1, maxA1 + 1, minA2, maxA2 + 1, _, _) and
      intersectRange(minS1, maxS1 + 1, minS2, maxS2 + 1, _, _)
    )
  }
}

string testInput() {
  result =
    "px{a<2006:qkq,m>2090:A,rfg}\npv{a>1716:R,A}\nlnx{m>1548:A,A}\nrfg{s<537:gd,x>2440:R,A}\nqs{s>3448:A,lnx}\nqkq{x<1416:A,crn}\ncrn{x>2662:A,R}\nin{s<1351:px,qqz}\nqqz{s>2770:qs,m<1801:hdj,R}\ngd{a>3333:R,R}\nhdj{m>838:A,pv}\n\n{x=787,m=2655,a=1222,s=2876}\n{x=1679,m=44,a=2067,s=496}\n{x=2036,m=264,a=79,s=2244}\n{x=2461,m=1339,a=466,s=291}\n{x=2127,m=1623,a=2188,s=1013}\n"
}

module TestImpl = Impl<testInput/0>;

string realInput() {
  result =
    "hz{m>3518:A,A}\nxjq{s<700:R,x>3290:A,a>2004:R,R}\ndn{x<1908:R,a>539:A,s>1576:R,kdn}\nql{m<3667:rpl,A}\njsd{m>1643:R,R}\ndvq{s<1083:R,x>2321:A,A}\nqzq{x<3660:A,a>2909:jnb,vhm}\npz{s>3001:jlf,zj}\ngb{s>236:tpj,mk}\nkgl{s<3549:nfm,a>2025:R,x>1769:A,A}\njkc{s>1836:A,x>1826:A,vt}\nzn{a<471:A,s<757:lmg,th}\nvhm{s<3774:A,a<2437:A,A}\ngq{x>3007:ngs,xmr}\nlz{x>314:R,a>1284:R,A}\ngsg{m>1029:R,x>3382:R,R}\ncqj{x<2250:A,A}\nczh{x<2534:ntq,s>296:nvl,cq}\nsjb{m>910:A,s>2975:A,R}\ngss{m<3349:R,R}\nsf{m<1613:A,x>1749:R,s<2024:R,R}\nqd{m<2979:R,s>420:A,s<211:mmr,hc}\nnm{m<2530:A,a<690:R,A}\ncf{s<2923:A,A}\ngqh{m<690:gzc,ft}\nkxg{s<868:A,s>881:R,x<2889:R,R}\nbqk{s>1277:rqv,a>1262:xrn,xtd}\njjf{s<2363:R,a>312:R,R}\nqlv{a>1656:rp,sx}\nczx{s<374:R,A}\ncvm{m<3623:A,a>3090:R,a<2883:R,A}\nnp{x<57:R,R}\ndf{a>2646:tct,qgd}\npq{m>3886:A,s>1300:A,A}\ngvj{x<3344:A,m<3208:A,x<3652:R,A}\nftk{s>183:czh,m<2812:dxs,mpj}\ngdl{a>2242:R,A}\ntpj{a>1952:R,x>414:A,a>1633:A,R}\nhd{m<746:A,x>3172:A,x<2654:lk,jjf}\npqj{m<2823:rlq,m>3109:rj,A}\nttj{s<1462:mj,A}\nvcl{x>2410:A,s>1991:A,x<2115:R,A}\ngsd{m>2665:A,x<2552:R,s<1074:A,A}\ndh{s<1213:A,bvg}\nxf{s>2328:pc,s<1137:jmc,tlf}\njkd{x>1888:cf,x<908:kc,A}\nnxd{m>3569:A,x<552:R,A}\nkjv{x<2636:zt,x<3183:lkx,m>3114:qrb,pn}\nkrp{s>3241:R,m<3498:A,A}\nsmm{m<734:A,R}\nph{a<3213:A,m>3216:R,A}\nnz{x<2386:dtq,s>2080:A,A}\nsgj{a<1835:R,A}\nqrb{a<955:cxr,m>3690:dc,tn}\nnk{x>795:qp,A}\nplm{m<1874:jbr,nkj}\nlc{x>454:A,x<266:R,A}\njj{a>2841:A,a<2118:A,R}\npj{m>3173:nxd,x<414:A,hdb}\nrh{x<3019:R,A}\nnfm{x>1631:R,A}\nblh{x<1029:pj,brl}\nppt{a<3642:R,m<1223:gsg,A}\nhk{a<2029:hpn,s<492:zbb,jt}\nnmj{s<207:R,m<3830:A,x<2241:A,R}\ndl{a<871:A,m>2275:A,A}\ncbs{s<609:vx,s<657:R,A}\nvf{m>3366:A,a>560:R,a>296:A,A}\nxq{a>1033:R,a<956:A,A}\npc{x>3394:A,x<3086:R,a>2727:A,A}\nnnk{m>2619:R,a>3006:hpp,jkh}\nzt{m>3191:zpb,bsq}\nvl{x<3532:A,s>887:A,R}\nlmg{m>3564:R,R}\nxrf{s>425:kq,m>2828:A,a>324:nm,fsk}\ntn{x<3644:zpz,m<3397:A,rch}\nhf{a<1446:A,x<2942:A,x<3022:A,R}\nbt{s<2790:lbf,a>1654:qpp,s>3238:nql,kjv}\ngg{a>2956:gsd,m<2713:dvq,R}\nmv{s>651:A,m<1448:A,x<146:A,A}\ntp{m>3253:gss,x>1334:A,ms}\npg{x<2282:R,a<1349:vg,m>2840:R,hfl}\nrch{x>3834:A,s<3078:R,A}\ncxr{s>2975:plt,x>3547:R,x<3385:gr,fxd}\nbk{m<3130:hkl,m<3476:tp,m>3712:bgc,skz}\nxbx{a>3426:rc,s<863:sd,hq}\nkd{s>1340:A,A}\nbjf{a<593:R,A}\nmhm{a>1647:A,a>1415:A,m<2372:A,A}\nfx{a<3216:vz,srj}\nml{a<2860:R,R}\nkzv{s<1301:A,R}\njkh{s<947:R,R}\npcl{m<3722:rvk,s>1134:pq,a<2815:R,A}\nbm{m<776:A,a>3600:R,A}\nhrt{s<674:R,x>2588:R,a>2018:R,A}\nlqj{x<676:kfp,x>856:lt,br}\ndhd{m<2607:R,A}\nqcv{x<1535:kl,R}\nszq{x>2379:hd,a>306:dn,s<1822:hkd,dns}\ntqq{a<522:mb,R}\nlkx{a<878:tqq,sbt}\nvcc{x>109:R,m<1781:R,m<1933:np,R}\ngdz{a>3532:A,A}\nvgt{m<1215:vcl,jcg}\nbxp{s>1485:A,s<563:R,m>1025:A,A}\nbmd{x<2839:rxh,a>2312:nmm,s>1414:krn,bq}\nrhg{s<152:A,R}\ncz{a<1432:ztv,xfr}\nvsd{a>2247:R,a>1946:R,a>1844:A,R}\nmqt{x<3172:R,x<3581:R,x>3825:R,R}\ntq{x<2593:R,A}\nfj{m<3481:rh,tv}\ngx{m>2883:R,R}\nch{m<517:nk,pd}\nmbs{s>1219:A,s<1197:R,x>2230:R,R}\nrr{s<927:A,x>1452:A,x<1372:R,R}\ncgj{s<3063:R,A}\nbbv{s>1112:R,R}\ntqz{a>3803:nbb,psq}\nncz{m>3717:R,a<634:R,R}\njcg{s<2537:R,m<1343:R,A}\njt{x<1325:pbb,R}\nkzb{m>3653:jqx,m>3482:gf,x>3249:xsk,rjx}\nrqv{m<3538:zzl,s<1338:tkq,R}\nhsb{a>1037:R,x>870:R,A}\njb{x<2075:A,x<2506:lxt,A}\nvbk{a<2870:gjb,a>3277:A,dp}\njqs{a<1324:A,m>2852:R,a>1529:R,A}\nqm{a>3573:A,R}\nrzk{x<557:vmp,s<83:tvm,m<3236:mc,ncz}\nts{s<3733:fh,tfn}\nnsj{a<1336:A,a>1857:A,a>1584:A,R}\nvt{a>1102:R,m>2866:R,A}\nzkj{x>2500:R,a<467:A,R}\nbs{m<724:A,x>3306:fhb,x>3204:A,kdl}\nplt{x>3572:R,m<3702:R,s<3130:R,A}\njfc{x>924:sf,m<1651:lz,mpg}\nknp{m>564:A,m<232:A,s>2339:A,R}\nqgd{a<1965:cm,A}\ntdm{m>2827:R,m>2718:A,a>3015:R,A}\nhgj{s>1445:zq,xrb}\nztv{m>1357:qsl,tpx}\nfhb{s>1607:R,a<3027:R,A}\nkhd{a>3834:R,m>3473:R,R}\ntrc{s>512:rrk,m>2509:nd,s>326:sxh,cng}\nhr{a>656:A,m>2850:R,x>3389:A,A}\nrp{a>2022:R,R}\ngjb{a<2267:A,R}\nfd{x<1052:vtp,a<949:jrn,hk}\nfz{a>980:R,A}\nccg{m>2905:R,a>2436:R,R}\nqlg{m>1037:R,R}\nnhh{x>2581:ql,m>3642:nmj,a>1170:kpf,jdt}\njlf{x>3531:R,s>3219:A,A}\nnd{s<173:vbb,s>385:npn,bxz}\nfhj{m<724:R,a>3762:R,x>3053:R,R}\ntx{m>1717:A,m<1555:R,R}\nqz{x<3152:R,m<1947:R,tz}\nbln{m>1964:A,R}\nlh{s<2877:xqk,R}\nxhd{x<3255:ps,dz}\nkrn{m>1099:gm,gjk}\nhpp{a<3169:A,s<938:R,A}\nsrj{m<3640:A,A}\nfgh{m>1756:R,m>1722:R,s>1813:A,R}\ngrd{x<1684:A,x>2484:A,x<2179:R,A}\nmpj{a<3142:A,x<2258:tpz,R}\njv{x>3146:sq,s>269:R,cb}\nvc{a<1112:A,m<1598:jng,m<1694:A,fgh}\ntct{a>3518:R,jp}\nszk{x>2702:A,s>821:A,x<2020:A,R}\ntt{x<3002:A,x<3058:R,s<2845:R,A}\nxv{a<1832:A,s<1237:A,s<1251:A,R}\nvrq{a<1062:jtr,R}\nfbz{m>2837:A,A}\nms{m<3212:A,A}\ndz{x>3696:dk,m<3179:A,A}\nsq{x<3517:A,m<1576:R,m>1616:A,R}\nvrv{x>2073:A,m<3335:A,a>3264:R,A}\nnx{s>284:R,A}\nbq{a<1964:ddh,zmr}\nghk{a<441:R,A}\nbr{a<2694:smm,x>795:zzv,s<2123:A,R}\nkmr{x>1717:A,a>3663:A,s<3538:R,R}\nhc{s<318:A,R}\nvr{a<399:A,x>2222:A,m>3016:A,A}\ncl{m>2530:ct,x<1855:qvv,dh}\nvmp{x>236:R,x>131:A,A}\nvq{s>526:vb,a>2478:kf,jv}\nmdb{a<380:R,m<2455:R,A}\ncpb{s<1179:dzj,dj}\nssz{s>1128:A,R}\nmmr{m<3107:R,R}\nddh{x>3498:tm,R}\nmk{x>561:A,s>98:R,x>197:R,R}\njdn{a>1667:R,xlx}\nskh{s<2941:R,a<1171:R,s<3134:A,A}\nktr{s>2122:rk,a<757:tsm,vrq}\njs{x<1491:A,R}\njnr{s<796:R,s>1213:R,A}\nxd{x<2458:hv,x<3129:cgj,m>2807:qbb,pz}\nhfl{s<300:A,R}\nzxt{s<2782:A,s<3589:A,s>3804:R,R}\nkf{s<213:kht,s<412:nx,m>1587:A,ksp}\njdt{a<424:R,x<2178:R,a<690:A,tvf}\ndns{s<2857:xbf,s<3399:llz,a>196:fdf,jsq}\ndd{x>1491:R,s<398:A,A}\njmc{a<2988:xjq,s>688:A,trj}\nhkd{a<163:jnr,R}\nzmb{m<3165:pls,gpv}\nmb{m<3218:A,m>3585:A,m>3436:A,R}\nmsx{x<3666:R,m<3398:R,a<3006:R,A}\nvz{s<1252:A,A}\nbvc{s<449:R,a>3035:A,R}\ngz{x<3316:zcz,qzq}\nbb{m<2381:R,x>2178:R,a<1435:R,A}\nqch{s>2944:A,m>1485:A,s>2282:R,R}\nfdf{a>234:R,a<219:R,m<652:R,R}\nbqr{m<1655:A,A}\ndjn{x>2008:nt,a<993:jns,x<1955:R,sjr}\nxbf{m<712:A,x>1977:R,A}\nqpp{s<3361:xd,x>2233:gz,s>3593:ts,sxk}\nsrq{s<567:nhh,s<733:kzb,a<1151:nfr,fj}\nvgz{x<2442:R,x>3163:A,s<1109:A,A}\nspf{m>3098:A,a>1114:R,x<2359:vr,R}\nlk{m<1007:R,m<1155:A,A}\ncq{x<3030:R,m<3304:A,s>244:R,R}\nhpn{m>3374:A,s<535:R,R}\npnr{s<564:R,a>1040:A,x>573:knx,vd}\ncc{s>1430:mfd,A}\nfdb{s>349:R,s>228:A,s>81:A,A}\ncm{m<1985:R,x>2862:R,A}\nzg{x<2013:R,s>3441:A,R}\nth{s<768:A,s<776:R,m>3551:R,R}\nbvt{s<883:pxk,A}\nps{x<2852:R,a<1334:kj,R}\nxmr{x>2490:xs,x<2141:djn,m>2911:spf,pg}\ntsm{s<872:A,a<426:bln,x>1500:db,A}\nqsl{m<1825:gd,m>1995:tmb,m>1914:ktr,plm}\ntvf{s<308:A,m<3477:A,x>2430:A,R}\nnbb{a>3887:R,m<2823:A,khd}\njsq{m<806:R,a<125:R,R}\ngm{s<2956:R,m>1252:dfc,s>3550:R,R}\nkv{x>203:R,x<134:A,m<1920:R,R}\nbgc{m>3875:R,ssz}\nrxh{a<2551:vgt,jb}\npsq{s<967:dvk,m<3358:A,R}\nrg{x>249:R,x<137:A,A}\nrt{a>1268:R,a<1073:A,R}\nrcf{m<3157:A,x<3888:R,R}\nxtd{a<718:mbs,a>915:ss,a<801:R,A}\ntlf{m>331:A,a>2999:R,A}\nzl{a<2924:R,a<3347:A,m>592:R,R}\nkdl{x<3179:A,a>3060:A,A}\nxrn{s>1236:mdq,a<2044:A,gj}\ngj{a>2399:R,a<2219:A,s>1215:A,A}\nfq{s>518:A,x>3344:A,s>294:A,A}\nrb{a>3423:R,a>2952:A,x>915:R,R}\nbg{a<433:dd,A}\nzzv{x<828:R,s>2255:A,s>1152:R,R}\nlp{m<3249:A,s<3008:A,m<3278:A,R}\ncvd{a<2723:A,gdz}\nzcz{m>3081:A,a>2862:R,a>2373:A,R}\nqk{a<1277:R,m<3551:R,R}\nhj{m>3271:A,x<1007:A,R}\ntr{a<839:A,A}\nrld{s<823:R,m<2378:R,A}\nfzv{a<1192:mqd,a<1307:kg,nz}\ngpv{x>1141:R,jl}\nzbb{a>2244:ccg,x>1335:mmf,bh}\nss{m<3642:A,A}\nzdd{m<2602:xt,tdm}\nzqq{m>575:R,A}\nzzz{a>3102:vrv,a<2800:cqj,a<2999:A,bvc}\nkfp{x>515:ml,A}\ndxf{a>315:R,R}\nvb{m>1613:jsd,a>2462:szk,hsz}\nlpk{s>1135:lht,s>989:gg,nnk}\njtr{m<1957:A,a<935:R,A}\nls{x>1788:zg,js}\nsd{s>376:lxx,ftk}\nff{x>3648:R,a<3816:R,R}\ndvk{m>3204:A,R}\nnc{a<1279:A,x<2499:R,R}\ndtq{x<2009:A,R}\nrks{m<3222:R,R}\nin{m<2131:cz,mtv}\njd{s>1478:td,m>1696:df,s<981:vq,vlr}\nct{a>879:xv,m>3005:A,nv}\nlt{s>1942:zf,R}\nzfj{a<1034:zkj,rhg}\ndfc{m>1352:R,a>2004:R,x<3229:R,A}\nvrx{m<3175:xxm,R}\nngs{a<867:lrj,x>3362:nj,qd}\nszg{a>2781:A,m<3156:R,a<2714:R,R}\nxg{m<2460:R,R}\nhh{x>2365:R,A}\nkg{m<614:tq,a<1245:R,x>2659:bxp,R}\nht{s<3063:R,x<1179:A,R}\ngv{x<2021:R,R}\nmqd{m<718:A,s<2597:R,qxn}\njng{m>1474:A,R}\nhzf{m>655:A,A}\ntdc{x<221:A,m>2804:R,A}\ntpx{x<1414:ch,a<816:szq,fzv}\nvxm{s<304:R,x<383:tdc,m<2773:mdb,A}\ndxs{x<2545:jcn,s<100:xg,s<153:A,jmj}\ngbb{x<2907:mvc,m<543:xf,x>3553:gqh,hjt}\nvg{s<356:A,m<2800:A,A}\ntkq{m>3809:A,s<1316:R,x>1546:R,R}\nzhp{m<1606:A,a>167:A,m<1712:A,R}\nzj{a<3026:A,s>2915:A,R}\nrkl{m>3409:R,A}\nrj{s>1336:A,R}\nskz{s<1142:vgz,m>3577:R,m<3533:nc,qk}\nbf{m>2781:zz,a>3752:A,a<3606:fdb,R}\nzs{a<2108:R,a<2506:R,tx}\ndj{s>1374:pzt,m>3269:bqk,s<1274:cl,sdn}\ndk{m>2966:R,s<971:R,m<2476:R,A}\nkdn{a<435:R,s<659:R,A}\ntv{a>1679:vsd,m<3686:R,x<2729:R,A}\nnfx{s<3034:A,x>3884:A,A}\nknx{x>816:R,x<702:A,R}\nrc{x<1712:fnm,tqz}\njbr{a<852:A,R}\ncgb{a<789:A,s<1835:A,m>3623:rt,A}\nxqk{a<1905:R,a>2223:A,a>2093:A,A}\nrrk{s>719:rld,a<1094:cbs,qlv}\nbvg{m<2397:R,R}\nzb{x<3060:R,a<430:qr,csg}\nvd{x>278:A,R}\nqkc{a<3268:lzc,R}\nhsz{m<1538:A,s<813:A,A}\nfg{s>3518:R,a<3152:A,A}\nzf{a<2679:A,x>922:R,A}\nnfr{s<786:zn,s>828:qvz,zb}\nlsq{s<2128:R,x<1564:A,R}\nvlr{m>1602:kzv,s<1153:mqt,fvn}\npzt{a<1316:hgj,x>2214:cc,ttj}\nfxd{a>391:R,a>191:R,s<2888:A,A}\nnt{s>446:R,x<2086:A,A}\nbts{a>638:R,A}\nlmt{a<2621:tt,a<3304:cx,fhj}\nds{x<646:A,A}\nmpg{m<1752:A,A}\ntz{s<2648:A,a>3313:A,s<3179:A,A}\nbrk{a<277:A,a>456:R,A}\ndc{m>3795:R,a>1285:cqc,m<3754:skh,A}\nrgq{a>637:A,x>2228:R,R}\nlht{a>3119:A,s>1330:A,R}\nmvc{a<2677:sg,fl}\ncng{x>2909:tc,s<113:kpq,s>224:fz,zfj}\nqbb{s<3159:hz,s<3283:krp,msx}\nlrj{x>3540:A,m<2947:fq,A}\njcn{x>1192:A,m>2569:R,A}\nfcd{m<948:A,x<1316:ht,qch}\nqvz{m>3696:kxg,a<538:R,tr}\nmh{m<3314:grd,s<712:R,x<1541:A,cvm}\ngbz{a<622:R,A}\nntq{s>250:A,m>3001:R,x<845:A,R}\nqr{s<813:R,R}\nrl{x>2198:A,x>2022:A,R}\ncs{a<815:A,s>2641:A,m<1444:A,R}\njqx{a<941:A,a>1538:hrt,A}\nvx{m<2417:R,x>3122:R,A}\ngt{s>2144:bqr,a>368:A,x<2059:zhp,A}\nmdq{x<1604:R,x>2419:R,s<1260:R,A}\ngzc{m>604:hzf,zqq}\nkpq{x<2542:bb,x>2734:nxl,a>928:R,ghk}\ntvm{s>36:R,a<694:R,m<3038:R,R}\ncqc{m>3736:R,a>1421:A,A}\ncx{x>2986:R,A}\nnxl{m>2336:R,a>1436:R,R}\nlbf{a>1678:ks,mml}\nmx{m<1054:A,a<2830:R,A}\nxlx{m>2271:R,a>1109:R,x<3278:R,A}\nxs{x<2732:A,m>3031:czx,x<2854:gzj,R}\nkm{x<2607:R,a>927:R,gvj}\npf{x>1306:rr,mx}\nqj{m<2324:brk,R}\njp{a>3169:R,s<612:R,a>2848:A,A}\nnmm{a<3403:sr,s<2153:sc,ppt}\nrpl{s>208:R,R}\ngjk{m>958:qlg,sjb}\nmc{s<140:R,s>158:A,a>577:R,A}\nqvv{s>1224:A,hsb}\ncb{m>1607:R,R}\nnvl{x<3257:R,a<3099:A,A}\nmmf{m<2967:A,A}\nkpf{s>198:rl,R}\nzmr{x<3388:vqn,R}\nrv{s<3061:R,R}\nnl{s<1931:pf,fcd}\nxrb{x<1432:R,A}\nkc{m<2063:R,A}\nrvk{s<1178:A,R}\nkfx{s>1262:R,x<1201:R,A}\nfb{s>2493:A,s>995:rg,m>1647:kv,mv}\npls{x<1059:ds,s<3787:R,x<1733:A,fqj}\nsr{a>2831:R,s<1861:vl,R}\nbxz{s<250:dhd,A}\nnhx{m>3054:R,R}\nlhq{m>650:R,x>2996:zl,s<1699:R,R}\nzz{x>740:A,m>3478:A,s>359:R,R}\nzd{s<2863:knp,R}\nsl{a>3038:qvb,xj}\nbh{x<1198:R,m<2785:A,R}\ntpz{m<3568:R,R}\nvtp{s>401:pnr,a>1078:gb,s<174:rzk,vxm}\nsp{m<1518:cs,s<2529:R,m<1688:A,A}\nxx{x>3480:R,x>3304:R,R}\ngzj{m<2860:A,a>1265:R,A}\nfnm{s>574:hj,bf}\nksp{s>456:A,R}\npxk{a>3069:R,s>481:A,R}\nxxm{x>2290:R,A}\ncsg{a>838:R,A}\npn{m<2473:sqj,a<1054:lts,qg}\nbxt{m<3605:A,s>674:A,R}\nkvs{s<3401:km,rks}\nvqn{m<1234:R,s<899:A,m<1365:R,R}\ndzj{s>1078:bk,x>2290:xhd,blh}\nhgz{a<561:A,s<3039:R,x>1054:R,R}\njns{s>319:A,m>2997:R,s<151:A,A}\nkj{m>3210:A,m>2599:R,A}\njnb{x>3800:R,a>3516:A,R}\npgg{x>1354:kd,m>2551:gbz,x>763:A,lc}\nsdn{a<991:pgg,s<1308:kzl,pqj}\nlxt{m<1151:R,x>2255:R,s>2561:A,R}\nnql{s<3500:kvs,x<2601:zmb,hp}\nnkj{x<1439:R,A}\nmfd{x<3094:A,x<3593:R,m<2791:R,R}\nnpn{s<446:R,R}\nrk{a<925:A,A}\nfh{m<3144:R,a>2601:rb,R}\nkq{x>1327:R,s<628:R,s<719:R,R}\nllz{x<1865:R,x<2062:R,m<533:R,A}\nft{s<1983:bbv,a<2323:gqm,a<3139:zxt,bm}\nmml{s>2364:vrx,m<3279:jkc,cgb}\nrlq{x>2132:R,m>2557:R,a>1746:A,A}\nprc{x>1012:nl,x>429:lqj,m>1338:nhr,dt}\ngqm{x>3726:A,s<2694:A,m<756:R,R}\nlvm{m<3367:A,s>598:A,x<2525:R,R}\ndb{m>1949:R,x>2355:R,A}\nfvh{m<1036:R,A}\nfsj{m>1663:A,x>2977:A,s>2939:R,A}\nmtv{s>1535:bt,a>2595:xbx,s>888:cpb,zjb}\nzq{x>2291:R,R}\nfsk{s>265:R,m<2431:A,s>111:A,A}\nlts{x>3595:bjf,hr}\ntmb{s>1466:jkd,qcv}\nxfr{x<1561:prc,m<833:gbb,m>1471:jd,bmd}\nzjb{x<1868:fd,m>3209:srq,m>2729:gq,trc}\ngf{m<3555:R,x<2969:bxt,m<3599:A,R}\nhgd{x<3424:jqs,x<3784:hcv,rcf}\ngr{m>3624:A,a>594:A,a>338:R,A}\nhcv{a<1292:A,m>3015:R,R}\nnj{m>3046:A,x<3685:fbz,m>2877:R,A}\nrjx{s<635:lvm,A}\njmj{m<2437:A,a<3023:R,A}\nhp{a>779:hgd,dxf}\nsqj{s<2972:R,m>2255:R,m<2212:rv,xx}\nvbb{s<93:A,a<1485:R,R}\nsc{x<3438:R,m<1135:A,a>3704:ff,qm}\nbrl{s<979:A,a<1569:R,s>1040:R,A}\nhkl{a>1206:A,rgq}\nsnt{a<3037:pcl,x>2181:qkc,fx}\nhv{m<2950:R,sdv}\nmj{a<1926:A,A}\ntm{s>687:R,A}\nsxh{x>2873:jdn,a>1033:mhm,a<613:qj,dl}\nsdv{m<3613:A,R}\nqg{s<2990:R,x<3664:gx,s<3085:nfx,R}\nvp{s<3458:R,a<3203:R,kmr}\nbsq{s<3005:R,A}\nqp{s<1699:A,A}\njl{s>3798:A,R}\nfvn{x>2512:A,s<1276:R,R}\nzzl{m>3437:R,x>2355:R,R}\nqxn{x<3126:R,m<1095:A,R}\npbb{m<3066:A,R}\nks{m<3192:cvd,lsq}\ntfn{a>3183:nhx,A}\ntrj{a<3362:A,m>290:A,x<3632:R,A}\nzpz{a<1354:R,s<3021:R,A}\nkl{m>2073:A,A}\nkht{a>3289:A,x<3178:R,A}\nxt{a>3063:A,x<2237:A,a>2887:A,A}\nfl{s>2668:fg,A}\nxsk{m<3311:nsj,a<1513:R,R}\ndt{s<2042:bvt,a>2530:zd,sgj}\ngd{a<620:gt,x>2444:vc,a>1108:jfc,sp}\nnv{s>1240:R,m>2836:R,a>353:A,R}\ntd{a<2465:lh,m<1779:fsj,qz}\nhq{m<3025:lpk,m>3391:snt,sl}\nkzl{m>2636:A,m<2420:R,R}\nhdb{m<2705:A,m<2892:A,s<988:A,R}\nlzc{s<1244:R,A}\npd{x>814:bts,fvh}\nfqj{a>577:R,x>2263:A,x>2013:R,A}\nhjt{x>3133:bs,s>2231:lmt,s>1243:lhq,jj}\ntc{a<1040:R,a<2061:R,R}\nsx{m>2430:R,a>1441:R,R}\njrn{m<3177:xrf,bg}\nsjr{s>434:R,R}\nsbt{a>1333:hf,m<2974:xq,A}\nxj{s<1140:szg,a>2875:hh,m>3181:gv,A}\nzpb{m>3499:hgz,m<3296:lp,s>2976:vf,rkl}\ndp{a>3031:A,a>2953:A,R}\nlxx{s>575:mh,m<2984:zdd,zzz}\nsxk{x<1180:vbk,a>2579:vp,s<3501:ls,kgl}\nqvb{s<1124:R,x<2353:kfx,ph}\nsg{x>2195:R,m>320:gdl,a>2241:A,R}\nnhr{a>2999:fb,x<176:vcc,zs}\n\n{x=1853,m=1718,a=852,s=421}\n{x=1856,m=768,a=800,s=33}\n{x=2847,m=1317,a=3464,s=932}\n{x=2618,m=561,a=3141,s=132}\n{x=148,m=476,a=2620,s=457}\n{x=388,m=1384,a=860,s=100}\n{x=1929,m=115,a=349,s=290}\n{x=3086,m=2861,a=1622,s=48}\n{x=31,m=423,a=315,s=1698}\n{x=174,m=907,a=49,s=122}\n{x=541,m=15,a=242,s=2732}\n{x=1552,m=95,a=350,s=1981}\n{x=741,m=981,a=3076,s=2421}\n{x=849,m=166,a=1512,s=1803}\n{x=13,m=1454,a=146,s=2150}\n{x=957,m=67,a=56,s=360}\n{x=243,m=368,a=1375,s=878}\n{x=890,m=274,a=421,s=83}\n{x=474,m=87,a=2601,s=767}\n{x=993,m=106,a=3272,s=1520}\n{x=102,m=295,a=545,s=2670}\n{x=2084,m=1274,a=2583,s=1055}\n{x=1440,m=57,a=2201,s=1181}\n{x=189,m=4,a=515,s=3434}\n{x=164,m=15,a=38,s=368}\n{x=643,m=2265,a=1169,s=1196}\n{x=133,m=323,a=36,s=737}\n{x=1924,m=859,a=590,s=268}\n{x=1308,m=668,a=627,s=64}\n{x=1277,m=1203,a=2822,s=164}\n{x=143,m=1445,a=1323,s=1941}\n{x=876,m=577,a=159,s=2538}\n{x=877,m=664,a=121,s=238}\n{x=578,m=1677,a=99,s=825}\n{x=94,m=697,a=629,s=786}\n{x=1108,m=1064,a=5,s=597}\n{x=416,m=2871,a=946,s=208}\n{x=1055,m=20,a=1258,s=1102}\n{x=85,m=144,a=1934,s=120}\n{x=747,m=2995,a=841,s=809}\n{x=205,m=94,a=959,s=1002}\n{x=251,m=1836,a=475,s=381}\n{x=363,m=765,a=187,s=536}\n{x=1823,m=1509,a=361,s=1068}\n{x=136,m=765,a=260,s=899}\n{x=1752,m=178,a=310,s=227}\n{x=318,m=617,a=1396,s=564}\n{x=1371,m=196,a=2487,s=2149}\n{x=2723,m=926,a=1502,s=1746}\n{x=146,m=448,a=181,s=2032}\n{x=1501,m=2536,a=1073,s=476}\n{x=850,m=900,a=29,s=2148}\n{x=984,m=128,a=1750,s=1273}\n{x=65,m=740,a=648,s=1147}\n{x=660,m=1068,a=1249,s=1061}\n{x=289,m=1612,a=710,s=1181}\n{x=1872,m=258,a=1788,s=508}\n{x=492,m=1178,a=125,s=618}\n{x=849,m=1586,a=3172,s=1776}\n{x=398,m=1499,a=737,s=645}\n{x=115,m=227,a=154,s=622}\n{x=415,m=505,a=388,s=338}\n{x=104,m=1398,a=921,s=164}\n{x=421,m=1201,a=3389,s=456}\n{x=661,m=237,a=292,s=283}\n{x=143,m=845,a=1391,s=1900}\n{x=777,m=141,a=207,s=3834}\n{x=780,m=927,a=62,s=430}\n{x=2947,m=1361,a=5,s=50}\n{x=3493,m=134,a=1163,s=2043}\n{x=135,m=456,a=58,s=1093}\n{x=1244,m=758,a=450,s=1089}\n{x=290,m=2583,a=1692,s=1164}\n{x=200,m=713,a=192,s=2113}\n{x=1164,m=57,a=3464,s=2020}\n{x=1023,m=137,a=1328,s=1460}\n{x=612,m=597,a=101,s=427}\n{x=2247,m=891,a=1224,s=2817}\n{x=870,m=3099,a=1275,s=305}\n{x=2099,m=1353,a=1867,s=55}\n{x=264,m=153,a=2560,s=1307}\n{x=274,m=125,a=167,s=27}\n{x=208,m=88,a=1676,s=1450}\n{x=5,m=161,a=3312,s=1403}\n{x=2294,m=1021,a=4,s=1766}\n{x=2683,m=91,a=441,s=2454}\n{x=503,m=1775,a=492,s=2809}\n{x=517,m=19,a=609,s=1051}\n{x=603,m=313,a=211,s=2889}\n{x=1663,m=342,a=1651,s=1501}\n{x=305,m=1190,a=232,s=1049}\n{x=3469,m=86,a=883,s=1897}\n{x=654,m=1526,a=741,s=186}\n{x=2611,m=959,a=541,s=1131}\n{x=3122,m=827,a=1701,s=1953}\n{x=594,m=1973,a=475,s=191}\n{x=134,m=1169,a=125,s=554}\n{x=4,m=401,a=176,s=3228}\n{x=2978,m=7,a=309,s=3088}\n{x=1187,m=2241,a=221,s=185}\n{x=666,m=1214,a=144,s=197}\n{x=176,m=30,a=208,s=3302}\n{x=1581,m=2530,a=596,s=244}\n{x=1264,m=1345,a=16,s=53}\n{x=122,m=424,a=2194,s=3612}\n{x=859,m=7,a=8,s=2258}\n{x=1346,m=211,a=113,s=34}\n{x=663,m=1448,a=2323,s=1344}\n{x=112,m=141,a=708,s=2131}\n{x=312,m=1345,a=1836,s=337}\n{x=5,m=1556,a=1244,s=848}\n{x=1589,m=233,a=21,s=933}\n{x=2173,m=2390,a=180,s=864}\n{x=1645,m=1798,a=773,s=297}\n{x=3292,m=109,a=1124,s=613}\n{x=482,m=1353,a=784,s=3347}\n{x=1189,m=3164,a=1874,s=1053}\n{x=495,m=431,a=831,s=35}\n{x=686,m=915,a=1823,s=809}\n{x=766,m=1004,a=1354,s=307}\n{x=3352,m=1047,a=471,s=148}\n{x=155,m=1449,a=997,s=345}\n{x=117,m=93,a=1355,s=14}\n{x=1710,m=1171,a=875,s=1402}\n{x=1339,m=1068,a=2676,s=354}\n{x=1306,m=29,a=1186,s=2010}\n{x=179,m=532,a=581,s=1137}\n{x=349,m=2778,a=1035,s=1522}\n{x=1779,m=831,a=91,s=447}\n{x=2267,m=267,a=370,s=177}\n{x=684,m=3595,a=349,s=55}\n{x=3394,m=422,a=1182,s=1468}\n{x=1902,m=359,a=956,s=2143}\n{x=3729,m=1383,a=799,s=887}\n{x=2182,m=855,a=1277,s=195}\n{x=608,m=1985,a=83,s=3923}\n{x=2768,m=233,a=1538,s=2232}\n{x=59,m=1225,a=270,s=983}\n{x=1804,m=2039,a=957,s=705}\n{x=460,m=1115,a=1049,s=376}\n{x=27,m=144,a=1421,s=2553}\n{x=838,m=2998,a=563,s=3050}\n{x=142,m=466,a=479,s=1125}\n{x=715,m=565,a=32,s=138}\n{x=156,m=668,a=507,s=2073}\n{x=1926,m=267,a=3414,s=554}\n{x=1253,m=1693,a=2019,s=360}\n{x=398,m=2354,a=1778,s=643}\n{x=954,m=525,a=1508,s=1607}\n{x=37,m=31,a=149,s=803}\n{x=212,m=383,a=1288,s=145}\n{x=39,m=639,a=364,s=1277}\n{x=2519,m=1272,a=31,s=2869}\n{x=162,m=1170,a=449,s=516}\n{x=2101,m=1142,a=2348,s=156}\n{x=915,m=2517,a=1793,s=2079}\n{x=540,m=856,a=2704,s=3}\n{x=414,m=836,a=71,s=1790}\n{x=2796,m=1429,a=60,s=928}\n{x=52,m=88,a=610,s=517}\n{x=1019,m=1532,a=2767,s=632}\n{x=1443,m=441,a=228,s=642}\n{x=328,m=595,a=947,s=936}\n{x=463,m=2650,a=104,s=3234}\n{x=789,m=62,a=281,s=257}\n{x=293,m=18,a=56,s=62}\n{x=9,m=665,a=556,s=426}\n{x=1141,m=1351,a=760,s=599}\n{x=370,m=839,a=102,s=1985}\n{x=2295,m=197,a=2136,s=181}\n{x=545,m=1190,a=1118,s=1373}\n{x=1488,m=1075,a=265,s=1678}\n{x=890,m=3,a=376,s=406}\n{x=75,m=318,a=14,s=264}\n{x=920,m=63,a=238,s=3394}\n{x=1787,m=3530,a=2762,s=5}\n{x=316,m=1158,a=1934,s=1069}\n{x=573,m=195,a=105,s=564}\n{x=1821,m=2141,a=579,s=808}\n{x=323,m=2219,a=61,s=208}\n{x=140,m=1375,a=46,s=2408}\n{x=358,m=529,a=220,s=31}\n{x=203,m=789,a=585,s=868}\n{x=2118,m=884,a=828,s=362}\n{x=388,m=2794,a=2062,s=372}\n{x=862,m=2303,a=1032,s=196}\n{x=725,m=1153,a=478,s=1423}\n{x=1353,m=313,a=2826,s=31}\n{x=2985,m=183,a=1256,s=734}\n{x=446,m=417,a=1970,s=122}\n{x=3598,m=2237,a=38,s=247}\n{x=455,m=1138,a=109,s=527}\n{x=697,m=1815,a=3009,s=530}\n{x=30,m=49,a=497,s=871}\n{x=866,m=400,a=1041,s=2446}\n{x=304,m=512,a=1530,s=194}\n{x=1213,m=2841,a=152,s=553}\n{x=477,m=547,a=534,s=2815}\n{x=411,m=765,a=70,s=1005}\n{x=1767,m=1973,a=872,s=494}\n"
}

module RealImpl = Impl<realInput/0>;

select 1
