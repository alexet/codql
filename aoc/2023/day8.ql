import lib

module Impl<inStr/0 input> {
  import Helpers<input/0>

  string direction(int k) { result = lines(0).charAt(k) }

  string part(int n, int k) {
    result = lines(n).regexpCapture("([A-Z0-9]*) = \\(([A-Z0-9]*), ([A-Z0-9]*)\\)", k)
  }

  class Node extends string {
    int n;

    Node() { this = part(n, 1) }

    Node getLeft() { result = part(n, 2) }

    Node getRight() { result = part(n, 3) }

    Node getReachable() {
      result = getLeft()
      or
      result = getRight()
    }
  }

  int cycleLen() { result = lines(0).length() }

  Node nodeAt(int n) {
    n = 0 and result = "AAA"
    or
    exists(Node prev | prev = nodeAt(n - 1) and prev != "ZZZ" |
      direction((n - 1) % cycleLen()) = "L" and
      result = prev.getLeft()
      or
      direction((n - 1) % cycleLen()) = "R" and
      result = prev.getRight()
    )
  }

  int stepCount() { nodeAt(result) = "ZZZ" }

  int numNodes() { result = count(Node n) }

  int reachableCount(Node start) { result = count(start.getReachable*()) }

  cached
  Node nodeAt2(int n, Node start) {
    n = 0 and start.matches("__A") and result = start
    or
    exists(Node prev |
      prev = nodeAt2(n - 1, start) and
      n < (reachableCount(start) * cycleLen())
    |
      direction((n - 1) % cycleLen()) = "L" and
      result = prev.getLeft()
      or
      direction((n - 1) % cycleLen()) = "R" and
      result = prev.getRight()
    )
  }

  int rankFoundIndex(Node start, Node found, int r, int n) {
    result = rank[n](int pos | nodeAt2(pos, start) = found and r = pos % cycleLen())
  }

  int cycleLen(Node start) {
    exists(Node found, int r |
      result = rankFoundIndex(start, found, r, 2) - rankFoundIndex(start, found, r, 1)
    )
  }

  int cycleStart(Node start) {
    result = min(Node found, int r | 
        found.matches("__Z") 
        | rankFoundIndex(start, found, r, 2)) - cycleLen(start)
  }

  predicate isStartAndLen(Node start, int len, int startPos) {
    len = cycleLen(start) and startPos = cycleStart(start)
  }


  int finishOffsetsRelativeToCycle(Node start) {
    exists(Node finish, int r |
      result = rankFoundIndex(start, finish, r, 2) % cycleLen(start)
      and finish.matches("__Z")
    )
  }

  // The above are all zero, so CRT would give 0
  // We then need to advance by LCM until we reach the cycle.

  // The cycle is always a subset of the direction cycle, so we can just
  // advance by the direction cycle.
  int cycleLen2(Node start) { result = cycleLen(start) / cycleLen() }

  int cycleMod(Node start) {
    result = cycleLen(start) % cycleLen()
  }

  Node rankedStart(int k) { result = rank[k](Node n | n.matches("__A")) }

  bindingset[a, b]
  int lcm(int a, int b) { result = (a * b) / a.gcd(b) }

  int totalCycleLenUpTo(int k) {
    k = 0 and result = 1
    or
    k > 0 and result = lcm(totalCycleLenUpTo(k - 1), cycleLen2(rankedStart(k)))
  }


  // All the lengths a prime and gcd stops working, but we know it is one
  float totalCycleLenUpToAssumingPrime(int k) {
    k = 0 and result = 1
    or
    k > 0 and result = totalCycleLenUpToAssumingPrime(k - 1) * cycleLen2(rankedStart(k))
  }

  int totalCycleLen() { result = totalCycleLenUpTo(max(int k | exists(totalCycleLenUpTo(k)))) }


  float totalCycleLenAssumingPrime() { result = totalCycleLenUpToAssumingPrime(max(int k | exists(totalCycleLenUpToAssumingPrime(k)))) }

  float fullCycleLen() {
    result = totalCycleLen().(float) * cycleLen().(float)
  }


  float fullCycleLenAssumingPrime() {
    result = totalCycleLenAssumingPrime().(float) * cycleLen().(float)
  }
}

string testInput() {
  result =
    "RL\n\nAAA = (BBB, CCC)\nBBB = (DDD, EEE)\nCCC = (ZZZ, GGG)\nDDD = (DDD, DDD)\nEEE = (EEE, EEE)\nGGG = (GGG, GGG)\nZZZ = (ZZZ, ZZZ)\n\n"
}

string testInput2() { result = "LLR\n\nAAA = (BBB, BBB)\nBBB = (AAA, ZZZ)\nZZZ = (ZZZ, ZZZ)" }

string testInput3() {
  result =
    "LR\n\n11A = (11B, XXX)\n11B = (XXX, 11Z)\n11Z = (11B, XXX)\n22A = (22B, XXX)\n22B = (22C, 22C)\n22C = (22Z, 22Z)\n22Z = (22B, 22B)\nXXX = (XXX, XXX)"
}

string realInput() {
  result =
    "LRRRLRRLRLRRRLRLLLLRRRLRLRRLRLRLRRLRRRLRRLRRRLRLLLRRLRRLRRLRRLRRLLLLLRLRLRRRLRLLRRLRLRRRLRRLRRRLLLRRLRRLRRLRRRLRLRLRRLLRRRLRRLRRRLRRRLRRRLRLRRLRRLRRLRRRLRLRRLRRLLRRRLRRLRRLRRRLRLRLRRLLRRRLLRRLRRRLRRRLRLRRLLRRRLRLRRLLRRLRLRRRLRLRRRLRRLRRLRRLRRRLRRRLRLLRRLRRLLRRLRRRLRRLRLRLRRRLLLRRLRLRRLRRLRLRLLRLRRLRLRLRRRR\n\nXKM = (FRH, RLM)\nMVM = (JVG, TRK)\nBXN = (SJH, XFB)\nKJS = (QRD, QRD)\nLCQ = (DQL, TRQ)\nTRP = (FBR, BLD)\nHSQ = (QQN, KSN)\nJHK = (RLD, VBR)\nKGJ = (RNB, NFN)\nNDD = (KFR, HQL)\nJXD = (XTC, TKR)\nFTT = (SBD, HNS)\nNLV = (CDM, TRS)\nBHL = (CHX, SGB)\nHNV = (LCB, TFS)\nMPX = (JDL, FCZ)\nXVA = (VTR, PLN)\nHHC = (SXC, HCH)\nRNF = (TKJ, PTJ)\nTJN = (JRQ, KJR)\nCRR = (XHF, CTT)\nGDH = (DKC, SMT)\nVFP = (TKC, NVL)\nDNV = (QPV, XBJ)\nKCK = (TFH, BQD)\nFCH = (QHV, GXS)\nBHK = (JSF, KKC)\nSKX = (FTL, SGQ)\nSXC = (HNG, JLL)\nTKD = (DMX, CMC)\nTKC = (PHF, RBK)\nGPM = (GGJ, XSG)\nTVK = (KGM, QVK)\nPFD = (HDT, XKB)\nLKV = (RVP, FJM)\nTHQ = (RLJ, TXM)\nDGG = (XJS, RTL)\nKFR = (LHR, CGQ)\nMXJ = (FPQ, CVB)\nLHC = (VJX, BKX)\nFTH = (MST, FBS)\nFXC = (TSP, HTP)\nQBN = (GNB, XKM)\nFQH = (MFC, XXD)\nQHX = (MDG, DCN)\nPPJ = (XMR, QPQ)\nJVV = (HGB, PSR)\nFBS = (GSP, KGK)\nLQP = (RDG, XRX)\nQHV = (CDP, LPG)\nGSP = (XPV, XKJ)\nCRM = (MFT, KRK)\nHNK = (SNT, HQR)\nVDK = (DPK, TBJ)\nRNP = (GCS, VJL)\nSMN = (TQJ, RNJ)\nLCB = (SXM, BHV)\nRNQ = (SHT, VKP)\nQSN = (JMC, JDC)\nTCQ = (NRR, MKG)\nDXQ = (JRQ, KJR)\nCXR = (FLP, PKR)\nHBS = (VCH, CKN)\nNJJ = (RTD, MPN)\nTTK = (DGH, MNF)\nPLN = (GPF, DNB)\nFCZ = (JRM, DJV)\nLQM = (VGQ, NCX)\nCLX = (LQP, MNG)\nGGA = (NDK, FBC)\nMCX = (DQB, MGR)\nNTT = (XVB, MPP)\nTGJ = (GMC, LLG)\nLML = (SVR, VJT)\nJBB = (BNX, HDJ)\nLHR = (SQL, FDM)\nNVL = (RBK, PHF)\nFVR = (QHX, SDQ)\nFHM = (FTC, BNF)\nBRF = (QDC, HFT)\nJPF = (DQM, DCX)\nTXM = (RQR, GRX)\nVPX = (PXQ, CPP)\nRPZ = (GHJ, LSN)\nJTV = (SXC, HCH)\nSXN = (KSB, TQT)\nSDP = (QNB, BJV)\nHPM = (FXN, TJL)\nVHF = (CLX, KXB)\nQBJ = (PDC, SQH)\nQQN = (KCK, GSG)\nPQC = (FBR, BLD)\nJDC = (BVL, PFD)\nKKH = (QMS, DVL)\nLGK = (NKX, SQS)\nLVL = (RVV, TMV)\nDXC = (TXB, GHN)\nSDQ = (DCN, MDG)\nNQD = (KLL, GVS)\nCFX = (MVN, SDR)\nRLM = (RKN, MRT)\nDQH = (SMT, DKC)\nGPV = (HGB, HGB)\nJRQ = (TKN, TTK)\nSTG = (DVH, CJB)\nLKT = (NPS, VHN)\nXHS = (HCG, QNM)\nDXA = (QQN, KSN)\nQFJ = (HFN, CJC)\nVLT = (XXX, PMJ)\nLGS = (PPV, TVK)\nPKR = (TTT, TCN)\nCKD = (CFS, VDQ)\nSTM = (BKN, PPR)\nKXB = (MNG, LQP)\nFCV = (MGP, JBF)\nXVP = (SDM, TQL)\nDBK = (GVG, PPH)\nHLM = (PBJ, CRF)\nVNR = (JJQ, MQQ)\nPVN = (VJR, JFV)\nMBD = (GPV, JVV)\nVJX = (MLK, JFT)\nDHC = (SXN, RCK)\nDQL = (GLC, JXV)\nPPG = (FGK, RLN)\nXKB = (QLN, LBV)\nNRR = (MTS, HBS)\nSQL = (FVX, QNF)\nMGR = (NDD, DVK)\nMQQ = (LGS, RHS)\nDCX = (RHR, QQM)\nJRM = (RSQ, CGB)\nHDJ = (SMJ, RXN)\nTVT = (TDQ, XHS)\nJSC = (TJL, FXN)\nJGR = (VFP, QSV)\nMSK = (MXF, JGT)\nBGT = (NKM, FCH)\nTGM = (MKL, QJP)\nXHQ = (XVL, CFT)\nQSV = (NVL, TKC)\nCFM = (DDP, RKF)\nKHQ = (VJR, JFV)\nJXH = (VVK, KNQ)\nGFP = (QQF, VDK)\nHRD = (QCD, CBV)\nDTN = (DCX, DQM)\nSLS = (XLN, TQM)\nHMC = (NDK, FBC)\nLTA = (LSN, GHJ)\nXBC = (TSC, CFM)\nMPP = (JCS, HNV)\nKKJ = (GQR, VCL)\nJPH = (KGX, LDG)\nJCS = (TFS, LCB)\nFBR = (PNM, QBT)\nHBC = (HBT, LML)\nHRV = (PTJ, TKJ)\nQPV = (HKV, MLB)\nHFT = (JRD, JHN)\nNHR = (XJD, HBV)\nTDQ = (QNM, HCG)\nCTT = (XBC, QXK)\nGVC = (CPP, PXQ)\nTRK = (KFP, QCS)\nCLK = (CPT, QFJ)\nDPB = (FQC, HBJ)\nDRQ = (KMR, VHF)\nCBX = (DHC, FRG)\nSDM = (DHD, LGK)\nRQR = (RVC, DVD)\nMNF = (SHF, PCD)\nRCK = (KSB, TQT)\nFXT = (VFN, PND)\nGHZ = (KSN, QQN)\nFHX = (NPL, RNQ)\nJKM = (JXH, BFR)\nCDP = (SLQ, HHM)\nJXT = (SFT, CXR)\nDXN = (FHM, MDX)\nLNN = (HBF, RQX)\nVCL = (BRF, FQQ)\nKJR = (TKN, TTK)\nVPS = (CFT, XVL)\nGBH = (LNN, LGM)\nMBR = (GNB, XKM)\nXSG = (SHP, DQF)\nDLG = (CJV, RKB)\nQCL = (TNX, JQR)\nMST = (KGK, GSP)\nHFJ = (LLH, SMV)\nRKN = (NRL, LFD)\nPSR = (SRD, JKH)\nCCS = (MGR, DQB)\nDGH = (SHF, PCD)\nCBV = (PQC, TRP)\nTDJ = (CDM, TRS)\nBMS = (JQJ, FVR)\nPRF = (CKX, GQQ)\nTFS = (SXM, BHV)\nBFR = (KNQ, VVK)\nBFN = (HTP, TSP)\nBHJ = (VKD, BGT)\nGNB = (FRH, RLM)\nNXT = (BFS, RDD)\nKHK = (QRD, XDK)\nDXP = (SRF, RQN)\nFPQ = (DXC, VQT)\nHMX = (DFN, KQB)\nJRB = (KJT, MPX)\nPCD = (MVM, GQG)\nGFL = (VGC, BBM)\nHKV = (QLG, DCG)\nSJH = (HBD, LQB)\nXJQ = (LQM, XFF)\nDCJ = (KGJ, FLQ)\nMSJ = (JBF, MGP)\nJMC = (PFD, BVL)\nMQF = (FXT, RFM)\nTQL = (DHD, LGK)\nHCR = (GKQ, PRF)\nMXF = (FHD, MBD)\nNKM = (QHV, GXS)\nCJB = (BSL, XNT)\nGTX = (BVX, XBF)\nXHF = (XBC, QXK)\nDGF = (TGM, HNC)\nDVH = (BSL, XNT)\nMXN = (VHF, KMR)\nNHM = (XBJ, QPV)\nQNF = (DXN, FFM)\nDQX = (DSH, BLL)\nSNT = (PTL, PRJ)\nJDP = (CFX, HDH)\nMTS = (CKN, VCH)\nCRF = (CVL, HFJ)\nTXB = (XTH, LCQ)\nJRD = (HLM, KMG)\nLTQ = (NPS, VHN)\nXFS = (TCQ, VQV)\nLDG = (BVJ, CRM)\nLBR = (JTV, HHC)\nFSH = (MPN, RTD)\nJJQ = (LGS, RHS)\nKVL = (HQR, SNT)\nCTR = (TMV, RVV)\nFTL = (GGD, TVT)\nMDG = (MXJ, QVB)\nVMC = (TLK, SKX)\nKGK = (XPV, XKJ)\nXFB = (HBD, LQB)\nXXX = (CKS, PRQ)\nXFF = (VGQ, NCX)\nRHR = (BMV, HBC)\nGMC = (BXN, GLX)\nSDR = (GTX, KHN)\nHTD = (JXD, HGK)\nGXS = (LPG, CDP)\nXMR = (DRB, HPG)\nXTC = (TCK, BRK)\nVDQ = (LBR, SDS)\nBSL = (DGD, QBJ)\nRVV = (DTN, JPF)\nPPH = (BFD, CBX)\nFQC = (THQ, PFJ)\nGJS = (DRQ, MXN)\nXVR = (HMC, GSZ)\nVSK = (PSF, KKH)\nMGD = (BCB, KLR)\nBNF = (BFT, TKD)\nRDG = (RKV, LBN)\nXKN = (JPT, XVR)\nHNS = (HMX, TRV)\nLFD = (JPH, SJP)\nGQQ = (HSQ, GHZ)\nXJS = (CTP, NXT)\nHBJ = (PFJ, THQ)\nSXM = (DXV, PBV)\nXXD = (DGF, TSH)\nJKH = (HJM, ZZZ)\nGHJ = (DPB, KHH)\nSSK = (SBD, HNS)\nSST = (DQK, LKV)\nHTC = (RLK, MLT)\nVCH = (DQX, PXL)\nHML = (KPK, XPX)\nKKS = (FQH, JRP)\nDDP = (JJK, XVP)\nSQS = (QSN, MHV)\nVPD = (RFV, XHX)\nGSZ = (FBC, NDK)\nJPX = (VGC, BBM)\nMGP = (CPQ, BGB)\nTCK = (VKS, RVL)\nVJC = (SVV, JXT)\nRTL = (NXT, CTP)\nQGH = (XLN, TQM)\nJRR = (BDL, HRD)\nNKH = (JHK, XHR)\nRTD = (JGR, CGP)\nFHD = (GPV, JVV)\nSPG = (SMN, CDN)\nJGT = (FHD, MBD)\nQVP = (TJN, DXQ)\nTPD = (KLG, BHK)\nPXQ = (GHB, MQF)\nHCG = (GDH, DQH)\nFPL = (LTQ, LKT)\nCFS = (LBR, SDS)\nPTL = (JLH, RBB)\nTSH = (TGM, HNC)\nXBF = (DBK, GPG)\nCHX = (NMG, VNR)\nKHN = (BVX, XBF)\nBLV = (BFR, JXH)\nDRR = (QFX, RLS)\nMLB = (QLG, DCG)\nPBJ = (HFJ, CVL)\nSLQ = (KKJ, VVT)\nQJP = (BTM, TGJ)\nTTV = (HTD, DMF)\nXVG = (MPC, DGG)\nJFV = (SPG, CTS)\nDVD = (SFX, CRR)\nPRJ = (JLH, RBB)\nBKN = (SST, RPK)\nJJK = (TQL, SDM)\nJLL = (DPF, BPG)\nTMV = (JPF, DTN)\nMKG = (HBS, MTS)\nHJL = (LSN, GHJ)\nGGJ = (DQF, SHP)\nCMC = (DLG, TGH)\nXHR = (VBR, RLD)\nKMN = (SSK, FTT)\nDPF = (LHC, LKJ)\nPBV = (GXH, DGS)\nFBC = (NKH, KHP)\nTSC = (DDP, RKF)\nJBF = (CPQ, BGB)\nQLN = (RDR, TPD)\nQFX = (FHX, KDV)\nMLK = (VPD, HKC)\nDHD = (SQS, NKX)\nJSD = (DRQ, MXN)\nBJA = (DJV, JRM)\nTKJ = (PKD, VRR)\nCTP = (BFS, RDD)\nBFS = (GVC, VPX)\nMPC = (RTL, XJS)\nFMB = (DGG, MPC)\nGQR = (BRF, FQQ)\nMBC = (QVC, GBR)\nGKQ = (CKX, CKX)\nBGB = (BMS, HFP)\nPNM = (GFL, JPX)\nQXK = (TSC, CFM)\nXXL = (RLS, QFX)\nHBD = (GFP, XXJ)\nDQB = (DVK, NDD)\nTBP = (JPT, JPT)\nCDN = (TQJ, RNJ)\nXXJ = (VDK, QQF)\nCGB = (HPM, JSC)\nHJM = (XXL, DRR)\nCJV = (BHL, DJQ)\nPRR = (DVH, CJB)\nDSH = (VDB, VDB)\nDCN = (MXJ, QVB)\nMVN = (GTX, KHN)\nBFD = (FRG, DHC)\nTRS = (HML, TMD)\nHFN = (MGD, NDF)\nSRD = (HJM, HJM)\nTQT = (MGC, LTL)\nNHX = (JRP, FQH)\nFLP = (TCN, TTT)\nHFV = (XQP, DTC)\nTSP = (VXL, HTC)\nQNB = (NHR, XLX)\nMHV = (JMC, JDC)\nBKH = (QPQ, XMR)\nLTL = (RTM, DKN)\nSBD = (HMX, TRV)\nPPR = (RPK, SST)\nHBV = (GPM, HFQ)\nKSB = (LTL, MGC)\nVVK = (GXX, XFS)\nXRX = (LBN, RKV)\nCTS = (CDN, SMN)\nMFC = (DGF, TSH)\nSRF = (CKD, FBD)\nKKC = (PRG, HNF)\nRQN = (CKD, FBD)\nFQQ = (HFT, QDC)\nGXX = (VQV, TCQ)\nSMJ = (LPF, GBH)\nTJL = (TLL, RNP)\nQBT = (GFL, JPX)\nBVX = (GPG, DBK)\nSVR = (QVP, VJD)\nHSM = (FHR, FXJ)\nRXG = (JQR, TNX)\nCKX = (HSQ, HSQ)\nGPG = (PPH, GVG)\nGBR = (JSD, GJS)\nJXK = (JGT, MXF)\nXNT = (QBJ, DGD)\nSGB = (NMG, VNR)\nXLX = (HBV, XJD)\nMHQ = (NHX, KKS)\nRTJ = (DXP, KDT)\nHDT = (LBV, QLN)\nDJQ = (CHX, SGB)\nFHR = (PQN, HFV)\nGHN = (XTH, LCQ)\nRKF = (XVP, JJK)\nTCN = (JXK, MSK)\nNSQ = (PMJ, XXX)\nVQV = (NRR, MKG)\nJVG = (QCS, KFP)\nDGD = (PDC, SQH)\nKFP = (QCH, NQD)\nDKC = (DNV, NHM)\nRHS = (PPV, TVK)\nXHX = (NLT, DNG)\nPRG = (VMC, XNR)\nNMG = (MQQ, JJQ)\nLQB = (XXJ, GFP)\nMXR = (VTR, PLN)\nJLK = (FLQ, KGJ)\nMFT = (VFM, QDK)\nFXJ = (PQN, HFV)\nFBD = (VDQ, CFS)\nFNC = (SSK, FTT)\nMLT = (TBP, XKN)\nVTR = (GPF, DNB)\nTLK = (SGQ, FTL)\nFXN = (TLL, RNP)\nQRD = (LHL, LHL)\nSDS = (JTV, HHC)\nHGB = (SRD, SRD)\nTRV = (KQB, DFN)\nBVL = (HDT, XKB)\nPRN = (PPR, BKN)\nHTP = (VXL, HTC)\nDMF = (JXD, HGK)\nKDT = (SRF, RQN)\nVJD = (TJN, DXQ)\nJRP = (XXD, MFC)\nHBT = (SVR, VJT)\nVKS = (GHD, FTH)\nGGD = (XHS, TDQ)\nHFQ = (GGJ, XSG)\nDFQ = (KKS, NHX)\nVJL = (FCV, MSJ)\nXVL = (CPF, BQB)\nJSF = (PRG, HNF)\nBLR = (JKM, BLV)\nHNG = (DPF, BPG)\nRDR = (BHK, KLG)\nKGX = (CRM, BVJ)\nHQR = (PTL, PRJ)\nBCB = (SLS, QGH)\nXDK = (LHL, RFK)\nDFN = (HGM, MBC)\nPFJ = (RLJ, TXM)\nGHB = (FXT, RFM)\nTTB = (BJV, QNB)\nSQH = (RDX, VJC)\nPMJ = (CKS, PRQ)\nDJV = (RSQ, CGB)\nTKN = (MNF, DGH)\nFRG = (SXN, RCK)\nBVJ = (MFT, KRK)\nXNR = (SKX, TLK)\nQDC = (JHN, JRD)\nRLK = (TBP, TBP)\nRBB = (PRR, STG)\nVRR = (PVJ, FSV)\nSHP = (BKH, PPJ)\nLLH = (KMN, FNC)\nKJT = (JDL, JDL)\nDQK = (FJM, RVP)\nLBV = (RDR, TPD)\nRQX = (KJS, KHK)\nTNX = (FPL, RRV)\nVBR = (DFQ, MHQ)\nCPF = (FMB, XVG)\nLGM = (HBF, RQX)\nBCT = (DXP, KDT)\nXPX = (MBR, QBN)\nCVB = (DXC, VQT)\nVDB = (FGK, FGK)\nJXV = (NLV, TDJ)\nLLG = (BXN, GLX)\nMPN = (CGP, JGR)\nXJD = (HFQ, GPM)\nQCH = (KLL, GVS)\nKRK = (VFM, QDK)\nGQG = (TRK, JVG)\nSHF = (MVM, GQG)\nCRS = (BLV, JKM)\nNRL = (SJP, JPH)\nRFM = (PND, VFN)\nFLQ = (NFN, RNB)\nZZZ = (DRR, XXL)\nGLX = (XFB, SJH)\nDQM = (QQM, RHR)\nPND = (PRN, STM)\nGBJ = (HDH, CFX)\nCGQ = (FDM, SQL)\nHKC = (RFV, XHX)\nDPK = (BHJ, DCV)\nHGK = (TKR, XTC)\nGXH = (RKK, VSK)\nGPF = (VPS, XHQ)\nBQB = (FMB, XVG)\nJQJ = (QHX, SDQ)\nSMT = (NHM, DNV)\nFTC = (TKD, BFT)\nNPS = (SDP, TTB)\nXTH = (TRQ, DQL)\nXKJ = (SBM, HCR)\nSHT = (JLK, DCJ)\nPSL = (KJT, KJT)\nRNJ = (SHJ, TTV)\nXBJ = (HKV, MLB)\nJFT = (HKC, VPD)\nXBH = (HDJ, BNX)\nHCH = (HNG, JLL)\nCFT = (BQB, CPF)\nQVK = (KHQ, PVN)\nVXL = (RLK, MLT)\nSJP = (LDG, KGX)\nBPG = (LKJ, LHC)\nJQR = (FPL, RRV)\nKMG = (PBJ, CRF)\nVVT = (GQR, VCL)\nBMV = (HBT, LML)\nFFM = (MDX, FHM)\nDCV = (VKD, BGT)\nHQL = (CGQ, LHR)\nSVV = (SFT, CXR)\nLKJ = (VJX, BKX)\nXLN = (HNK, KVL)\nVTB = (QFJ, CPT)\nVGQ = (PSL, PSL)\nPSF = (QMS, DVL)\nGVS = (HRV, RNF)\nRTM = (NJJ, FSH)\nDXV = (GXH, DGS)\nDVL = (VTB, CLK)\nPRQ = (QCL, RXG)\nVJR = (SPG, CTS)\nQVC = (JSD, GJS)\nPXL = (DSH, BLL)\nCPP = (MQF, GHB)\nFSV = (NTT, PJT)\nNFN = (HSM, KXF)\nGSG = (TFH, BQD)\nFGK = (MXR, MXR)\nGHD = (MST, FBS)\nTKR = (BRK, TCK)\nTRQ = (JXV, GLC)\nHFP = (FVR, JQJ)\nCKS = (RXG, QCL)\nKQB = (HGM, MBC)\nRLD = (MHQ, DFQ)\nCPQ = (HFP, BMS)\nKLG = (KKC, JSF)\nRRV = (LTQ, LKT)\nVKD = (NKM, FCH)\nGVG = (CBX, BFD)\nRLJ = (GRX, RQR)\nNPL = (VKP, SHT)\nSMV = (FNC, KMN)\nKPC = (BDL, HRD)\nQNM = (DQH, GDH)\nPHF = (BLR, CRS)\nRDD = (GVC, VPX)\nRLS = (KDV, FHX)\nQQM = (BMV, HBC)\nHNF = (VMC, XNR)\nBLD = (PNM, QBT)\nQPQ = (DRB, HPG)\nVJT = (QVP, VJD)\nHPG = (FRV, TTM)\nTQJ = (TTV, SHJ)\nFJM = (JDP, GBJ)\nRKB = (BHL, DJQ)\nKLR = (QGH, SLS)\nBBM = (RTJ, BCT)\nPDC = (RDX, VJC)\nNDF = (KLR, BCB)\nDVK = (HQL, KFR)\nMGC = (RTM, DKN)\nBNX = (RXN, SMJ)\nTBJ = (DCV, BHJ)\nBRK = (RVL, VKS)\nNKX = (QSN, MHV)\nDCG = (JBB, XBH)\nRFV = (DNG, NLT)\nCDM = (HML, TMD)\nLBN = (JRR, KPC)\nDRB = (FRV, TTM)\nNDK = (NKH, KHP)\nDMX = (TGH, DLG)\nMKL = (BTM, TGJ)\nKHH = (HBJ, FQC)\nTFH = (CCS, MCX)\nBHV = (DXV, PBV)\nCVL = (LLH, SMV)\nNCX = (PSL, JRB)\nVQT = (TXB, GHN)\nGRX = (DVD, RVC)\nRKV = (KPC, JRR)\nQQF = (TBJ, DPK)\nKNQ = (XFS, GXX)\nRKK = (KKH, PSF)\nMNG = (RDG, XRX)\nPPV = (KGM, QVK)\nBDL = (QCD, CBV)\nQCD = (PQC, TRP)\nKLL = (HRV, RNF)\nBJV = (XLX, NHR)\nKSN = (GSG, KCK)\nRVL = (FTH, GHD)\nDTC = (CTR, LVL)\nKPK = (MBR, QBN)\nHDH = (SDR, MVN)\nLPF = (LNN, LGM)\nQMS = (VTB, CLK)\nRSQ = (HPM, JSC)\nQDK = (VLT, NSQ)\nVFN = (STM, PRN)\nCJC = (MGD, NDF)\nCGP = (QSV, VFP)\nRNB = (HSM, KXF)\nFDM = (FVX, QNF)\nPKD = (PVJ, FSV)\nKGM = (PVN, KHQ)\nTTT = (MSK, JXK)\nVFM = (VLT, NSQ)\nLHL = (HJL, HJL)\nTTM = (XJQ, VLQ)\nSHJ = (HTD, DMF)\nRVC = (CRR, SFX)\nFRV = (VLQ, XJQ)\nDKN = (FSH, NJJ)\nCPT = (CJC, HFN)\nVGC = (BCT, RTJ)\nFRH = (MRT, RKN)\nQCS = (QCH, NQD)\nKMR = (CLX, KXB)\nRVP = (JDP, GBJ)\nNLT = (BFN, FXC)\nFVX = (FFM, DXN)\nSBM = (GKQ, GKQ)\nKDV = (RNQ, NPL)\nGLC = (TDJ, NLV)\nVKP = (DCJ, JLK)\nMDX = (BNF, FTC)\nPJT = (MPP, XVB)\nJLH = (PRR, STG)\nQVB = (FPQ, CVB)\nQXZ = (PLN, VTR)\nKHP = (XHR, JHK)\nVHN = (TTB, SDP)\nTGH = (RKB, CJV)\nJHN = (KMG, HLM)\nSFT = (FLP, PKR)\nKXF = (FHR, FXJ)\nLPG = (HHM, SLQ)\nBLL = (VDB, PPG)\nMRT = (LFD, NRL)\nBFT = (CMC, DMX)\nPTJ = (VRR, PKD)\nTLL = (GCS, VJL)\nBQD = (MCX, CCS)\nRXN = (GBH, LPF)\nHNC = (QJP, MKL)\nRFK = (HJL, RPZ)\nPVJ = (PJT, NTT)\nAAA = (XXL, DRR)\nXPV = (SBM, HCR)\nDGS = (VSK, RKK)\nHBF = (KJS, KHK)\nRPK = (LKV, DQK)\nDNG = (FXC, BFN)\nDNB = (XHQ, VPS)\nJPT = (HMC, HMC)\nCKN = (DQX, PXL)\nTMD = (XPX, KPK)\nRLN = (MXR, QXZ)\nXQP = (CTR, LVL)\nHGM = (QVC, GBR)\nXVB = (JCS, HNV)\nBTM = (GMC, LLG)\nQLG = (XBH, JBB)\nGCS = (MSJ, FCV)\nSGQ = (GGD, TVT)\nVLQ = (LQM, XFF)\nRDX = (SVV, JXT)\nSFX = (XHF, CTT)\nPQN = (DTC, XQP)\nHHM = (KKJ, VVT)\nBKX = (JFT, MLK)\nDQF = (PPJ, BKH)\nTQM = (KVL, HNK)\nLSN = (KHH, DPB)\nJDL = (DJV, JRM)\nRBK = (BLR, CRS)\n"
}

module TestImpl = Impl<testInput/0>;

module TestImpl2 = Impl<testInput2/0>;

module TestImpl3 = Impl<testInput3/0>;

module RealImpl = Impl<realInput/0>;

select 1
//select RealImpl::stepCount(), RealImpl::stepCount2()
