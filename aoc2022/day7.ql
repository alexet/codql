import lib

module Impl<inStr/0 input> {
  newtype TFileOrFolder =
    TFile(int i) { exists(fileLines(i)) } or
    TFolder(int i) { exists(cdLines(i)) or i = 0 }

  string inputParts(int i) { result = Helpers<input/0>::lines(i) }

  string fileLines(int i) {
    result = inputParts(i) and result.regexpMatch("[0-9]+ [a-z]+(\\.[a-z]+)?")
  }

  string dirLines(int i) { result = inputParts(i) and result.regexpMatch("dir [a-z]+") }

  string cdLines(int i) {
    exists(string line | line = inputParts(i) and result = line.regexpCapture("\\$ cd ([a-z]+)", 1))
  }

  predicate cdUpLines(int i) { exists(string line | line = inputParts(i) and line = "$ cd ..") }

  Folder dirAfter(int i) {
    result.getIndex() = i
    or
    (exists(dirLines(i)) or exists(fileLines(i)) or lsLines(i)) and
    result = dirAfter(i - 1)
    or
    cdUpLines(i) and result = dirAfter(i - 1).getParent()
  }

  predicate lsLines(int i) { exists(string line | line = inputParts(i) and line = "$ ls") }

  class FileOrFolder extends TFileOrFolder {
    abstract string toString();

    abstract Folder getParent();

    abstract int getSize();
  }

  class File extends FileOrFolder, TFile {
    int getIndex() { this = TFile(result) }

    string getDefiningText() { result = fileLines(getIndex()) }

    override Folder getParent() { result = dirAfter(getIndex()) }

    override int getSize() {
      result = getDefiningText().regexpCapture("([0-9]+) [a-z]+(\\.[a-z]+)?", 1).toInt()
    }

    string getName() { result = getDefiningText().regexpCapture("[0-9]+ ([a-z]+(\\.[a-z]+)?)", 1) }

    override string toString() { result = getName() }
  }

  class Folder extends FileOrFolder, TFolder {
    int getIndex() { this = TFolder(result) }

    override Folder getParent() { result = dirAfter(getIndex() - 1) }

    language[monotonicAggregates]
    override int getSize() { result = sum(FileOrFolder x | x.getParent() = this | x.getSize()) }

    string getName() {
      result = cdLines(getIndex())
      or
      getIndex() = 0 and result = "/"
    }

    override string toString() { result = getName() }
  }

  Folder rootFolder() { result.getName() = "/" }

  int rootFolderSize() { result = rootFolder().getSize() }

  int freeSpace() { result = 70000000 - rootFolderSize() }

  int requiredSpace() { result = 30000000 - freeSpace() }

  int deletableDirSize() { result = min(Folder f | f.getSize() > requiredSpace() | f.getSize()) }
}

module TestImpl = Impl<testInput/0>;

module RealImpl = Impl<realInput/0>;

select sum(TestImpl::Folder f | f.getSize() < 100000 | f.getSize()),
  sum(RealImpl::Folder f | f.getSize() < 100000 | f.getSize()), TestImpl::deletableDirSize(),
  RealImpl::deletableDirSize()

string testInput() {
  result =
    "$ cd /\n$ ls\ndir a\n14848514 b.txt\n8504156 c.dat\ndir d\n$ cd a\n$ ls\ndir e\n29116 f\n2557 g\n62596 h.lst\n$ cd e\n$ ls\n584 i\n$ cd ..\n$ cd ..\n$ cd d\n$ ls\n4060174 j\n8033020 d.log\n5626152 d.ext\n7214296 k"
}

string realInput() {
  result =
    "$ cd /\n$ ls\ndir ddgtnw\ndir dtmbp\ndir dzbfsf\ndir fwrlqs\n305959 jjq.hjd\ndir qjnnw\n$ cd ddgtnw\n$ ls\ndir gftgshl\ndir grct\n57336 tbqpqfgd.wvz\n267191 vqms\ndir wtgzgmvr\n$ cd gftgshl\n$ ls\ndir mtshhn\ndir smnslwd\ndir znbs\n$ cd mtshhn\n$ ls\n244930 fsclsm\n197930 vnnf\n$ cd ..\n$ cd smnslwd\n$ ls\n205127 dbtvp.mbr\ndir grct\n270601 hcjtjptg\n146538 lsqvg.zmm\n310443 vnnf\n84541 vqms\n$ cd grct\n$ ls\n20977 jjq.hjd\n$ cd ..\n$ cd ..\n$ cd znbs\n$ ls\n192316 pjrpqc.gwh\n5233 tnqpmbjf.prg\n$ cd ..\n$ cd ..\n$ cd grct\n$ ls\n297156 qzlmfj.lhc\n104088 vnnf\n$ cd ..\n$ cd wtgzgmvr\n$ ls\ndir cfvjph\ndir jzdqctm\n153202 slcz\n$ cd cfvjph\n$ ls\n201215 tlms\n$ cd ..\n$ cd jzdqctm\n$ ls\ndir hnbjcm\n112648 jjq.hjd\n319899 lhzjrmsd\n118481 pclps\n226538 pfnmnm\ndir vdzsn\n148960 wmvd\ndir zvh\n$ cd hnbjcm\n$ ls\n147907 ddgtnw.tpg\ndir hgh\n107668 qjpfhmw.gts\ndir qvnbfdq\ndir tlms\ndir wlvg\n$ cd hgh\n$ ls\n64701 smnslwd.hnd\n$ cd ..\n$ cd qvnbfdq\n$ ls\n36206 dzbfsf.qsr\ndir dzfpqb\ndir rvdlmnqv\n13989 tlms.jgl\n145493 vqms\n$ cd dzfpqb\n$ ls\n259317 dzbfsf.mwc\n36195 rtgrs.hff\n$ cd ..\n$ cd rvdlmnqv\n$ ls\ndir smnslwd\n$ cd smnslwd\n$ ls\n141659 gflcq\n315323 mwszdwvg\n$ cd ..\n$ cd ..\n$ cd ..\n$ cd tlms\n$ ls\n263149 gwws.zcb\n$ cd ..\n$ cd wlvg\n$ ls\n42151 vqms\n$ cd ..\n$ cd ..\n$ cd vdzsn\n$ ls\n301547 smnslwd.hzc\n$ cd ..\n$ cd zvh\n$ ls\n111901 bsnmdtzq.mjp\n$ cd ..\n$ cd ..\n$ cd ..\n$ cd ..\n$ cd dtmbp\n$ ls\ndir cscpfcjv\ndir hdjs\ndir jcrb\ndir spmc\ndir spwsfpww\n$ cd cscpfcjv\n$ ls\n260848 qzcffqvp\n$ cd ..\n$ cd hdjs\n$ ls\ndir tlms\n$ cd tlms\n$ ls\n174135 fwpwgz\n$ cd ..\n$ cd ..\n$ cd jcrb\n$ ls\n77666 nqtvhszf\n198488 smnslwd\n40032 vnnf\n$ cd ..\n$ cd spmc\n$ ls\ndir hhwzwqzq\n319757 hlgvsbg\ndir jbrftqj\n$ cd hhwzwqzq\n$ ls\n43088 mrlnrp.nqs\n206555 vnnf\n$ cd ..\n$ cd jbrftqj\n$ ls\n296407 flb\n315927 fnbvwh.lcf\n$ cd ..\n$ cd ..\n$ cd spwsfpww\n$ ls\ndir ddgtnw\ndir hzb\ndir smnslwd\n74678 smnslwd.crg\n130878 tlms\n239208 tlms.hjr\n$ cd ddgtnw\n$ ls\n133732 gqddds\ndir grct\n240907 lslgfrm.fct\n64110 rtgrs.hff\ndir tlms\n275504 zvwjph.svd\n$ cd grct\n$ ls\n18055 fvnm\n$ cd ..\n$ cd tlms\n$ ls\n54154 vqms\n$ cd ..\n$ cd ..\n$ cd hzb\n$ ls\n178568 hmdszw\n132701 pzsfzr.zqz\ndir smnslwd\n$ cd smnslwd\n$ ls\n286526 dtcrb.tzw\n214568 smnslwd\n$ cd ..\n$ cd ..\n$ cd smnslwd\n$ ls\n118657 ccmmrv.wgs\n$ cd ..\n$ cd ..\n$ cd ..\n$ cd dzbfsf\n$ ls\n30773 grct.lbw\ndir jttqnbvn\n188768 pmdjrf.nqc\ndir ptbps\ndir tllwm\n176302 vqms\n$ cd jttqnbvn\n$ ls\n9663 jjq.hjd\n$ cd ..\n$ cd ptbps\n$ ls\n132576 jzfs.hpq\ndir pwclsbw\n$ cd pwclsbw\n$ ls\ndir dzbfsf\n$ cd dzbfsf\n$ ls\n157147 smnslwd.jcg\n$ cd ..\n$ cd ..\n$ cd ..\n$ cd tllwm\n$ ls\ndir pcbgr\ndir smnslwd\ndir svc\n$ cd pcbgr\n$ ls\ndir grct\n65990 gvlc.ptr\ndir jtqg\n108430 pljrmjb.hld\ndir smtbvvpn\ndir vqjdpt\n130683 vqms\n$ cd grct\n$ ls\n155740 hcstcmpz\n156312 rtgrs.hff\n317800 vnnf\n$ cd ..\n$ cd jtqg\n$ ls\n151962 rtgrs.hff\n181794 vwzsf\n$ cd ..\n$ cd smtbvvpn\n$ ls\n272000 fgqp.mhf\ndir mqgzwzn\ndir mspltflh\ndir smnslwd\n21242 vnnf\ndir vzjfv\ndir wnbtllq\n$ cd mqgzwzn\n$ ls\ndir rhp\n$ cd rhp\n$ ls\n297744 jjq.hjd\n$ cd ..\n$ cd ..\n$ cd mspltflh\n$ ls\n32927 rlwp.phz\n109360 vlpzz\n$ cd ..\n$ cd smnslwd\n$ ls\n172760 vqjgbzd.glg\n$ cd ..\n$ cd vzjfv\n$ ls\ndir dcrlnllf\ndir ddgtnw\ndir pjhnl\ndir twfpbs\n$ cd dcrlnllf\n$ ls\n19043 thrvjqmj.smd\n$ cd ..\n$ cd ddgtnw\n$ ls\n301193 fdh.pls\n$ cd ..\n$ cd pjhnl\n$ ls\n305148 dqfwn.zhg\ndir dzbfsf\n34622 smnslwd.nzj\n$ cd dzbfsf\n$ ls\n227330 bdmbnm.zpl\n232365 cfmhqlhp.qvj\n$ cd ..\n$ cd ..\n$ cd twfpbs\n$ ls\ndir rfn\ndir vdr\n$ cd rfn\n$ ls\n72138 grct\n$ cd ..\n$ cd vdr\n$ ls\n19296 vqms\n$ cd ..\n$ cd ..\n$ cd ..\n$ cd wnbtllq\n$ ls\n283471 grct.vmq\n285265 sqqj\n248581 trgqdwsc.zjc\n$ cd ..\n$ cd ..\n$ cd vqjdpt\n$ ls\n271132 hprsbjzw.lnr\n$ cd ..\n$ cd ..\n$ cd smnslwd\n$ ls\n4812 bcg.vwj\ndir ddgtnw\n30986 pwl.frb\ndir tlms\ndir vrwwh\ndir wwbdc\n304408 wwvvhr\n$ cd ddgtnw\n$ ls\n303604 fsclsm\n71614 jlpzljjl.vzw\n110905 mzlj.qjz\n56751 pnhjdbnt\n$ cd ..\n$ cd tlms\n$ ls\n36089 bpnhvpdf.spq\ndir ddgtnw\ndir grct\n97469 jjq.hjd\ndir jlz\ndir nhvvs\ndir ptzptl\ndir rsqtp\ndir sgbnjmwq\ndir smnslwd\n$ cd ddgtnw\n$ ls\ndir hwnfv\ndir jsdmffq\n268127 ndwhj\n255789 qzlfsmm\n230625 vnnf\n$ cd hwnfv\n$ ls\n224423 fzrj\n$ cd ..\n$ cd jsdmffq\n$ ls\ndir dzbfsf\n$ cd dzbfsf\n$ ls\n283246 zrfjlcg.sct\n$ cd ..\n$ cd ..\n$ cd ..\n$ cd grct\n$ ls\n40705 sgpc.wfv\n$ cd ..\n$ cd jlz\n$ ls\ndir vrcb\n$ cd vrcb\n$ ls\n223815 gctvnv.rpb\n$ cd ..\n$ cd ..\n$ cd nhvvs\n$ ls\n10109 rtgrs.hff\n$ cd ..\n$ cd ptzptl\n$ ls\ndir chvn\n225860 grct\ndir hsp\ndir nglr\ndir qgbbv\n64084 swlgd.cjm\ndir tlms\n$ cd chvn\n$ ls\n314968 cbp\ndir ddgtnw\n282139 ddgtnw.ppr\n121887 vnnf\ndir wvrzs\n$ cd ddgtnw\n$ ls\n19170 dzbfsf.tmf\n160727 wqbdcw\n$ cd ..\n$ cd wvrzs\n$ ls\n263372 vnnf\n$ cd ..\n$ cd ..\n$ cd hsp\n$ ls\ndir dzbfsf\ndir pcs\ndir rjvmwmgm\n179166 rtgrs.hff\n284238 sgb.gjc\n44485 smlqjjbt.pfb\n260588 vqms\n$ cd dzbfsf\n$ ls\ndir ntmzsm\n$ cd ntmzsm\n$ ls\ndir drbl\ndir frnvqp\n258006 qhqss.hnm\n$ cd drbl\n$ ls\n244040 wccppjd.tcg\n$ cd ..\n$ cd frnvqp\n$ ls\n196291 pqwqbrdw\n$ cd ..\n$ cd ..\n$ cd ..\n$ cd pcs\n$ ls\n102603 bvmnrf\n219969 tlms\n$ cd ..\n$ cd rjvmwmgm\n$ ls\n73837 ddgtnw\ndir tlms\ndir tnpfpcz\n247155 vnnf\ndir zmvwl\n$ cd tlms\n$ ls\n183532 vqms\n$ cd ..\n$ cd tnpfpcz\n$ ls\ndir jjn\n274527 rtgrs.hff\n97897 ztpd\n$ cd jjn\n$ ls\ndir nlmt\n$ cd nlmt\n$ ls\n132838 mzdcb.gtf\n$ cd ..\n$ cd ..\n$ cd ..\n$ cd zmvwl\n$ ls\n184809 zzdl.lqq\n$ cd ..\n$ cd ..\n$ cd ..\n$ cd nglr\n$ ls\n216870 clfrgzv.lsh\ndir ddgtnw\n22735 mhpgvbh.phg\n200235 vqms\n84345 wjrzwlp\ndir ztbjwv\n$ cd ddgtnw\n$ ls\ndir zfdts\n$ cd zfdts\n$ ls\n13693 grct\n$ cd ..\n$ cd ..\n$ cd ztbjwv\n$ ls\ndir zzrsvbg\n$ cd zzrsvbg\n$ ls\ndir ddgtnw\n$ cd ddgtnw\n$ ls\n258910 tlms.hrh\n$ cd ..\n$ cd ..\n$ cd ..\n$ cd ..\n$ cd qgbbv\n$ ls\ndir crc\ndir prszvcp\ndir qwrnllw\n151124 rtqqp.wfv\n291754 vnnf\n279433 wgsjgqm.zrm\n$ cd crc\n$ ls\n257354 ffg\n258517 jjq.hjd\n$ cd ..\n$ cd prszvcp\n$ ls\n279284 fnwgcvw.dbg\n201788 grct.ssc\ndir mtlr\n$ cd mtlr\n$ ls\ndir vztmrn\n$ cd vztmrn\n$ ls\n84994 dzbfsf\n$ cd ..\n$ cd ..\n$ cd ..\n$ cd qwrnllw\n$ ls\ndir nsrhgbt\n$ cd nsrhgbt\n$ ls\ndir smnslwd\ndir vsnmq\n$ cd smnslwd\n$ ls\n128046 rtgrs.hff\n$ cd ..\n$ cd vsnmq\n$ ls\n15634 zpqp\n$ cd ..\n$ cd ..\n$ cd ..\n$ cd ..\n$ cd tlms\n$ ls\n240233 rtgrs.hff\n$ cd ..\n$ cd ..\n$ cd rsqtp\n$ ls\ndir grct\ndir hcsjjss\n$ cd grct\n$ ls\ndir ddgtnw\n27078 rtgrs.hff\n$ cd ddgtnw\n$ ls\n235401 hzpr\n107837 smnslwd.pqr\n$ cd ..\n$ cd ..\n$ cd hcsjjss\n$ ls\ndir jhhw\n18002 nptmmjz.pgj\ndir tlms\n$ cd jhhw\n$ ls\n282291 mcmndtb.mjj\n$ cd ..\n$ cd tlms\n$ ls\n159577 tlms.ghp\n$ cd ..\n$ cd ..\n$ cd ..\n$ cd sgbnjmwq\n$ ls\ndir ddgtnw\ndir qfc\n34331 tlms.mdr\n$ cd ddgtnw\n$ ls\n168852 vnnf\n63729 vqms\n$ cd ..\n$ cd qfc\n$ ls\n321148 ftjjdg\n185489 mlp.ssf\n195188 tlms\n$ cd ..\n$ cd ..\n$ cd smnslwd\n$ ls\ndir dzbfsf\n102016 grct.vmc\ndir gtjgtd\n41304 pbdh\n94958 tlms.tcf\n178471 vqms\n$ cd dzbfsf\n$ ls\ndir dvvcg\ndir dznc\n51706 hpzg.rwm\n179994 vqms\n$ cd dvvcg\n$ ls\ndir bsswp\n$ cd bsswp\n$ ls\n189827 gpzmg\n$ cd ..\n$ cd ..\n$ cd dznc\n$ ls\n3424 smnslwd\n$ cd ..\n$ cd ..\n$ cd gtjgtd\n$ ls\n152369 ddgtnw\n$ cd ..\n$ cd ..\n$ cd ..\n$ cd vrwwh\n$ ls\n308054 grct.hgj\n$ cd ..\n$ cd wwbdc\n$ ls\ndir zwvtdc\n$ cd zwvtdc\n$ ls\ndir jqtv\n$ cd jqtv\n$ ls\ndir qdd\n165188 smnslwd.hwz\n$ cd qdd\n$ ls\n319798 jjq.hjd\n$ cd ..\n$ cd ..\n$ cd ..\n$ cd ..\n$ cd ..\n$ cd svc\n$ ls\ndir ddgtnw\n133886 fsclsm\n107226 jjq.hjd\n259031 wtnbwg.sct\n$ cd ddgtnw\n$ ls\n124212 tlms.qws\n$ cd ..\n$ cd ..\n$ cd ..\n$ cd ..\n$ cd fwrlqs\n$ ls\n45167 fsclsm\n42603 qfq.pqh\n$ cd ..\n$ cd qjnnw\n$ ls\n228764 gnlhtvzt\ndir grct\n134749 jbs.jnd\n66187 jjq.hjd\ndir mqbbh\ndir nlwjn\ndir rdn\ndir shffbpjj\n154029 spjc\n$ cd grct\n$ ls\ndir ddgtnw\n98292 vnnf\n$ cd ddgtnw\n$ ls\ndir zrb\n$ cd zrb\n$ ls\n244157 vnnf\n$ cd ..\n$ cd ..\n$ cd ..\n$ cd mqbbh\n$ ls\ndir dqmhnq\ndir dzbfsf\n243785 fgzd.rlv\ndir grct\ndir gwlcnf\ndir rnl\ndir slnqt\ndir smnslwd\ndir tlms\n183073 tlms.cvt\ndir wgctf\n$ cd dqmhnq\n$ ls\n149913 dzpn.qsg\ndir hmfvzjz\n198969 rtgrs.hff\n$ cd hmfvzjz\n$ ls\ndir dzbfsf\ndir hthgs\n$ cd dzbfsf\n$ ls\n318705 cmgjqnb.wbq\n$ cd ..\n$ cd hthgs\n$ ls\ndir ljmsqbvz\n$ cd ljmsqbvz\n$ ls\n304509 dwrcjrw\n$ cd ..\n$ cd ..\n$ cd ..\n$ cd ..\n$ cd dzbfsf\n$ ls\n116769 ccgfzf.pmh\n$ cd ..\n$ cd grct\n$ ls\n246522 tlms.djc\n$ cd ..\n$ cd gwlcnf\n$ ls\n109428 vqms\n$ cd ..\n$ cd rnl\n$ ls\n80705 grct.ptv\ndir mtwrqwwl\n174651 smnslwd.glg\n30849 swgp\ndir tlms\n$ cd mtwrqwwl\n$ ls\ndir wtmgr\n$ cd wtmgr\n$ ls\n134164 tlms.qmv\n316076 vqms\n138038 wnv\ndir zsmmhfq\n$ cd zsmmhfq\n$ ls\n316061 tlms\n$ cd ..\n$ cd ..\n$ cd ..\n$ cd tlms\n$ ls\n224252 fsclsm\n4673 png.ntp\n$ cd ..\n$ cd ..\n$ cd slnqt\n$ ls\ndir lzzwbcnl\ndir mpdrjwgl\n$ cd lzzwbcnl\n$ ls\ndir lhltmghz\n$ cd lhltmghz\n$ ls\ndir hzhfgsfd\n212254 lcj.rsh\n$ cd hzhfgsfd\n$ ls\n36945 fsclsm\n$ cd ..\n$ cd ..\n$ cd ..\n$ cd mpdrjwgl\n$ ls\n176456 ctftvdhl.hzz\n79819 dzbfsf\n248804 jvlglnb.dpw\n$ cd ..\n$ cd ..\n$ cd smnslwd\n$ ls\n33395 vnnf\n$ cd ..\n$ cd tlms\n$ ls\ndir jdvhnpv\n317469 lzsrnpd\ndir tlms\n$ cd jdvhnpv\n$ ls\ndir pbwh\ndir vfn\n$ cd pbwh\n$ ls\n170653 smnslwd\n$ cd ..\n$ cd vfn\n$ ls\ndir mcdpp\n$ cd mcdpp\n$ ls\n294474 dzbfsf.hfn\n$ cd ..\n$ cd ..\n$ cd ..\n$ cd tlms\n$ ls\ndir lvqjfj\n$ cd lvqjfj\n$ ls\n250581 rtgrs.hff\n$ cd ..\n$ cd ..\n$ cd ..\n$ cd wgctf\n$ ls\n263836 crthpg.vlr\ndir ddgtnw\n256310 fsclsm\ndir mmlw\ndir qzq\ndir tlms\n209457 vqms\n$ cd ddgtnw\n$ ls\ndir nrfgg\n$ cd nrfgg\n$ ls\n278109 dzbfsf\n301844 vqlp.wzt\n$ cd ..\n$ cd ..\n$ cd mmlw\n$ ls\ndir gsvfvgn\n$ cd gsvfvgn\n$ ls\n4966 ddgtnw.rhb\n85130 pld.qtc\n$ cd ..\n$ cd ..\n$ cd qzq\n$ ls\n89149 pgrgt.jmm\n$ cd ..\n$ cd tlms\n$ ls\n84537 bzfznn.cdg\n$ cd ..\n$ cd ..\n$ cd ..\n$ cd nlwjn\n$ ls\ndir ddgtnw\ndir psdb\ndir vdmlzzgd\ndir zdzrn\n$ cd ddgtnw\n$ ls\n6932 dzbfsf.jjg\n$ cd ..\n$ cd psdb\n$ ls\n196117 bhwb.mfn\n127600 vschrflh.fgp\n$ cd ..\n$ cd vdmlzzgd\n$ ls\n5427 llch\n$ cd ..\n$ cd zdzrn\n$ ls\ndir lfpltz\n$ cd lfpltz\n$ ls\n157546 sffcz\n$ cd ..\n$ cd ..\n$ cd ..\n$ cd rdn\n$ ls\n133184 fsclsm\n186144 mrntdh.spz\n117372 spdlb.vmp\n245469 vjrjwfwl.zzt\n$ cd ..\n$ cd shffbpjj\n$ ls\ndir ccwnzd\ndir pcqbmmzt\n$ cd ccwnzd\n$ ls\n143939 zlwqpwdl.hbh\n$ cd ..\n$ cd pcqbmmzt\n$ ls\n196568 bqm\ndir ddgtnw\n169897 jppm.lfw\n188545 psm.lml\ndir rcnp\ndir sjhrvszs\n83840 vnnf\ndir vvh\ndir wzcqnz\ndir zfctl\n$ cd ddgtnw\n$ ls\n320675 dzbfsf\n$ cd ..\n$ cd rcnp\n$ ls\n60088 fsclsm\ndir grct\ndir qndvg\n153481 rzdzmm.prg\n$ cd grct\n$ ls\n23004 rfgbpbt.mhp\n166737 vqms\n$ cd ..\n$ cd qndvg\n$ ls\n181934 smnslwd.tpb\n$ cd ..\n$ cd ..\n$ cd sjhrvszs\n$ ls\ndir gfpzrd\n283172 rtgrs.hff\ndir tlms\n$ cd gfpzrd\n$ ls\n110715 rltrjpg.lch\n117420 vnnf\n$ cd ..\n$ cd tlms\n$ ls\n211543 cvcq.lqw\n132575 tlms\n$ cd ..\n$ cd ..\n$ cd vvh\n$ ls\ndir bscbv\ndir djzcnld\n276126 grct.tjl\ndir nlsstb\n$ cd bscbv\n$ ls\n116170 smnslwd.pvj\n295190 vqms\n$ cd ..\n$ cd djzcnld\n$ ls\n6635 dtnqpfqw.nlj\n27153 fzpnfnp.jbt\n164286 rlchrtlw\n231430 rtgrs.hff\n33326 wbfqtpjn.vsq\n$ cd ..\n$ cd nlsstb\n$ ls\n91522 dbpdbtvw\n221628 nfdgjsp.npf\n$ cd ..\n$ cd ..\n$ cd wzcqnz\n$ ls\n244122 fcqwl.nwt\ndir grct\n19950 jjq.hjd\n296817 nwcvl\ndir smnslwd\n$ cd grct\n$ ls\ndir ddgtnw\ndir qglfnbds\ndir wrthr\n$ cd ddgtnw\n$ ls\n287254 drwqt\n90776 gddwrgh.qls\n$ cd ..\n$ cd qglfnbds\n$ ls\ndir qzh\n$ cd qzh\n$ ls\n164079 bswc\n207352 dzbfsf\n203683 ftdjsfbg.lbl\n60925 sgmtn.llc\ndir wws\n$ cd wws\n$ ls\n111099 mjq.fjz\n$ cd ..\n$ cd ..\n$ cd ..\n$ cd wrthr\n$ ls\ndir ddgtnw\ndir jfv\ndir ndwlld\ndir nsnz\ndir vqql\n$ cd ddgtnw\n$ ls\n180911 dzbfsf\n301448 jjq.hjd\ndir mdmc\ndir nlls\n207270 vqms\ndir wsctbr\n$ cd mdmc\n$ ls\n267495 dzbfsf.mcl\n$ cd ..\n$ cd nlls\n$ ls\n221776 jjq.hjd\n$ cd ..\n$ cd wsctbr\n$ ls\n93502 fsclsm\n$ cd ..\n$ cd ..\n$ cd jfv\n$ ls\n129583 ddgtnw\n$ cd ..\n$ cd ndwlld\n$ ls\n217056 gtqc.zvq\n$ cd ..\n$ cd nsnz\n$ ls\ndir jhntl\n$ cd jhntl\n$ ls\n103365 trdnzfz\n$ cd ..\n$ cd ..\n$ cd vqql\n$ ls\n201664 smnslwd.gzj\n$ cd ..\n$ cd ..\n$ cd ..\n$ cd smnslwd\n$ ls\n318911 fsclsm\ndir jcvmgzc\n101015 rtgrs.hff\n$ cd jcvmgzc\n$ ls\n37799 jjq.hjd\n$ cd ..\n$ cd ..\n$ cd ..\n$ cd zfctl\n$ ls\ndir fmfgjw\ndir lbz\n$ cd fmfgjw\n$ ls\n159825 ddgtnw.bhf\n210407 jjq.hjd\n$ cd ..\n$ cd lbz\n$ ls\n206810 gbcqz.lgw\n20178 rtgrs.hff"
}
