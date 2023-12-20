import lib

module Impl<inStr/0 input> {
  import Helpers<input/0>

  string parts(int n, int k) {
    result = lines(n).regexpCapture("([RLUD]) ([0-9]+) \\(#([0-9a-f]{6})\\)", k)
  }

  string origDir(int n) { result = parts(n, 1) }

  int origLen(int n) { result = parts(n, 2).toInt() }

  string color(int n) { result = parts(n, 3) }

  signature string dirPred(int n);

  signature int lenPred(int n);

  module AreaImpl<dirPred/1 dir, lenPred/1 len> {

    predicate posAfter(int n, int x, int y) {
        n = -1 and x = 0 and y = 0
        or
        (
          dir(n) = "R" and posAfter(n - 1, x - len(n), y)
          or
          dir(n) = "L" and posAfter(n - 1, x + len(n), y)
          or
          dir(n) = "U" and posAfter(n - 1, x, y + len(n))
          or
          dir(n) = "D" and posAfter(n - 1, x, y - len(n))
        )
      }
    
      float area(int n) {
        exists(int y1, int y2, int x1, int x2 |
          posAfter(n - 1, x1, y1) and
          posAfter(n, x2, y2) and
          result = (y1 + y2).(float) * (x1 - x2).(float)
        )
      }
    
      int extraArea(int n) { result = len(n) }
    
      float totalArea() {
        // All the areas of the shapes + half the line lengths.
        // This double counts inside corners bun under count outside corners
        // so we add a 1 to the result to account for the remaining 4 outside corners.
        result = (sum(int n | | area(n) + len(n).(float)) / 2) + 1
      }
  }

  predicate p1Area = AreaImpl<origDir/1, origLen/1>::totalArea/0;

  int hexCharValue(string s) {
    s = "0" and result = 0
    or
    s = "1" and result = 1
    or
    s = "2" and result = 2
    or
    s = "3" and result = 3
    or
    s = "4" and result = 4
    or
    s = "5" and result = 5
    or
    s = "6" and result = 6
    or
    s = "7" and result = 7
    or
    s = "8" and result = 8
    or
    s = "9" and result = 9
    or
    s = "a" and result = 10
    or
    s = "b" and result = 11
    or
    s = "c" and result = 12
    or
    s = "d" and result = 13
    or
    s = "e" and result = 14
    or
    s = "f" and result = 15
  }

  string realLenPart(int n) { result = color(n).substring(0, 5) }

  int realLen(int n) {
    result = strictsum(int i | | 1.bitShiftLeft((4 - i)*4) * hexCharValue(realLenPart(n).charAt(i)))
  }

  string realDir(int n) {
    color(n).charAt(5) = "0" and result = "R" or
    color(n).charAt(5) = "1" and result = "D" or
    color(n).charAt(5) = "2" and result = "L" or
    color(n).charAt(5) = "3" and result = "U"
  }

  predicate p2Area = AreaImpl<realDir/1, realLen/1>::totalArea/0;
}

string testInput() {
  result =
    "R 6 (#70c710)\nD 5 (#0dc571)\nL 2 (#5713f0)\nD 2 (#d2c081)\nR 2 (#59c680)\nD 2 (#411b91)\nL 5 (#8ceee2)\nU 2 (#caa173)\nL 1 (#1b58a2)\nU 2 (#caa171)\nR 2 (#7807d2)\nU 3 (#a77fa3)\nL 2 (#015232)\nU 2 (#7a21e3)\n"
}

module TestImpl = Impl<testInput/0>;

string realInput() {
  result =
    "R 7 (#32c140)\nU 2 (#253c23)\nR 5 (#1e70a0)\nU 4 (#584ec3)\nL 5 (#24a120)\nU 4 (#1d03a3)\nL 3 (#7454a0)\nU 2 (#388563)\nL 6 (#4f9170)\nU 4 (#300bf3)\nL 3 (#2f6e10)\nU 3 (#1c2613)\nR 3 (#656dd0)\nU 4 (#281983)\nR 7 (#287620)\nU 3 (#55f513)\nR 4 (#160ca0)\nD 7 (#1fce03)\nR 3 (#110940)\nU 4 (#67bd83)\nR 4 (#342180)\nU 2 (#1c6a21)\nR 3 (#0fd3c0)\nU 6 (#00b231)\nR 5 (#417e02)\nU 2 (#012b21)\nR 4 (#571920)\nD 6 (#2bc391)\nL 5 (#06b610)\nD 4 (#539271)\nR 5 (#5dcf32)\nD 3 (#11a7b1)\nR 4 (#417e00)\nD 5 (#057e31)\nR 5 (#10a4f0)\nD 7 (#07c651)\nR 2 (#0defe0)\nD 6 (#52d041)\nR 4 (#523fc0)\nU 4 (#3641c1)\nR 4 (#572670)\nU 2 (#0ed9c3)\nR 4 (#6f9270)\nU 3 (#481a43)\nR 4 (#18df40)\nU 5 (#321e03)\nR 3 (#19c400)\nU 6 (#240bb1)\nR 3 (#262fc0)\nD 8 (#213861)\nR 2 (#106700)\nD 4 (#6e7721)\nR 6 (#106702)\nD 4 (#1a0ca1)\nR 3 (#306cf0)\nD 4 (#4e72e3)\nR 6 (#2ddd00)\nU 5 (#0246f3)\nR 8 (#34c980)\nU 5 (#0246f1)\nR 5 (#468770)\nU 5 (#3bddb3)\nR 6 (#407df2)\nU 4 (#0d4723)\nR 2 (#232d72)\nU 3 (#0d4721)\nR 5 (#458292)\nU 6 (#460723)\nR 4 (#1099d2)\nU 7 (#021263)\nR 2 (#00ecd2)\nU 4 (#3609a3)\nR 4 (#5c4702)\nD 6 (#3609a1)\nR 2 (#34fdf2)\nD 5 (#48cd93)\nR 3 (#2aca52)\nU 7 (#1f0081)\nR 3 (#6fe682)\nU 4 (#1f0083)\nR 3 (#172802)\nD 4 (#52f873)\nR 4 (#0b1672)\nD 4 (#396f83)\nR 5 (#341452)\nD 5 (#021783)\nR 3 (#5562e2)\nU 6 (#021781)\nR 2 (#02f832)\nU 6 (#2f0413)\nR 3 (#0f87f2)\nU 2 (#3a1313)\nR 4 (#4a2000)\nD 7 (#3bae21)\nR 4 (#2fd400)\nD 7 (#3bae23)\nR 5 (#220350)\nD 3 (#1657f3)\nL 5 (#344c22)\nD 6 (#0a57d3)\nL 5 (#371b92)\nD 4 (#07e0d1)\nL 4 (#44d3c2)\nU 4 (#6a8161)\nL 7 (#374952)\nD 5 (#016691)\nR 2 (#03a9f2)\nD 5 (#1f21b1)\nR 7 (#556402)\nD 7 (#314a01)\nR 4 (#227e70)\nD 4 (#5c5421)\nR 8 (#227e72)\nD 3 (#14e951)\nL 4 (#2ae662)\nD 3 (#191733)\nL 5 (#011812)\nD 4 (#0ff213)\nR 9 (#201fc0)\nD 5 (#5c2c53)\nR 6 (#201fc2)\nD 4 (#175033)\nR 3 (#011810)\nD 3 (#0ed613)\nR 5 (#4ff382)\nD 4 (#17b3e3)\nR 7 (#419812)\nD 3 (#235fd3)\nR 5 (#5bdb22)\nD 4 (#2200e3)\nL 3 (#257c12)\nD 4 (#2d0183)\nL 5 (#44ccf2)\nD 3 (#033a63)\nR 8 (#2231f0)\nD 3 (#1a6073)\nR 2 (#2fd740)\nD 5 (#694813)\nR 8 (#3cd170)\nD 3 (#160c33)\nR 6 (#4f1da0)\nD 3 (#1510d3)\nR 2 (#064c80)\nD 4 (#618e43)\nL 4 (#0fc960)\nD 4 (#00a603)\nL 4 (#653382)\nD 4 (#3d9143)\nR 2 (#2c5fc2)\nD 3 (#82c2a1)\nR 7 (#2df952)\nD 3 (#82c2a3)\nR 2 (#348192)\nD 4 (#1919f3)\nR 6 (#14a7f0)\nU 5 (#215203)\nR 5 (#304700)\nD 4 (#52ed03)\nR 5 (#4461a0)\nD 5 (#104b63)\nL 5 (#31ebc0)\nD 6 (#560291)\nR 8 (#014200)\nU 3 (#5b0f01)\nR 8 (#3f3940)\nU 2 (#0046d1)\nR 3 (#5de660)\nU 3 (#0df221)\nL 3 (#30b5a0)\nU 2 (#44d301)\nL 8 (#1c2c70)\nU 5 (#5c2051)\nR 3 (#4580f0)\nU 3 (#2baca1)\nR 7 (#293080)\nU 3 (#352e11)\nR 8 (#108020)\nU 6 (#596e43)\nR 5 (#347900)\nU 4 (#35b053)\nR 5 (#2f9c80)\nU 4 (#5a9481)\nR 7 (#13e580)\nD 4 (#348a11)\nR 3 (#0d7c90)\nD 4 (#1397c3)\nR 5 (#5b5830)\nD 6 (#236813)\nR 3 (#1fcbb2)\nD 3 (#600003)\nR 6 (#2852a2)\nD 2 (#0e0633)\nR 3 (#4c9292)\nU 3 (#495b13)\nR 5 (#602c52)\nU 5 (#495b11)\nL 5 (#4c54d2)\nU 4 (#53acb3)\nR 4 (#3e3bc0)\nU 4 (#044403)\nR 7 (#363620)\nU 4 (#596a83)\nR 3 (#504600)\nU 7 (#4701f3)\nR 5 (#46a042)\nU 8 (#6f7593)\nR 5 (#09a5c2)\nU 5 (#096273)\nR 5 (#09d900)\nD 8 (#7096f1)\nR 4 (#509250)\nU 4 (#136681)\nR 2 (#2564d0)\nU 10 (#2cbcc1)\nR 3 (#2564d2)\nD 4 (#01cfc1)\nR 3 (#30de40)\nD 10 (#6afe81)\nR 3 (#417690)\nD 4 (#6b2053)\nL 7 (#4be090)\nD 4 (#2b4381)\nL 5 (#3027a0)\nU 4 (#485431)\nL 3 (#2f60d2)\nD 5 (#3f3751)\nL 3 (#2f60d0)\nD 6 (#0a1ac1)\nL 6 (#003d70)\nD 3 (#32b021)\nR 4 (#6dca90)\nD 5 (#507281)\nR 2 (#436f00)\nD 5 (#23c6a1)\nR 3 (#537db0)\nD 4 (#2aec01)\nR 7 (#4ec940)\nU 4 (#0d1c73)\nR 2 (#302510)\nU 3 (#1fac81)\nL 6 (#2bd470)\nU 5 (#1fac83)\nR 6 (#32a8a0)\nU 7 (#0d1c71)\nR 5 (#06d530)\nD 6 (#6bfe71)\nR 4 (#022af2)\nD 10 (#2999c1)\nR 2 (#147bf2)\nD 3 (#37c0e1)\nR 8 (#8349e2)\nD 4 (#37c0e3)\nR 2 (#27ea02)\nD 2 (#2999c3)\nR 9 (#0db3d2)\nD 4 (#43efc1)\nR 3 (#4ae5e2)\nD 3 (#342641)\nR 4 (#571b60)\nD 3 (#035e71)\nR 5 (#064d50)\nU 2 (#126b71)\nR 6 (#056180)\nU 8 (#51b3c1)\nR 5 (#5a9570)\nU 4 (#51b3c3)\nR 8 (#25a5e0)\nU 2 (#15c851)\nR 3 (#039590)\nD 6 (#55a361)\nR 6 (#33d960)\nD 4 (#21b371)\nR 2 (#74bb50)\nD 3 (#33a773)\nL 4 (#18e2e0)\nD 3 (#388313)\nL 8 (#282be0)\nD 2 (#5f3b13)\nL 2 (#5ad2c0)\nD 3 (#2b9d53)\nL 2 (#82fea2)\nD 10 (#035653)\nL 3 (#18e2e2)\nD 2 (#0f36f3)\nL 3 (#3c8d70)\nD 3 (#0e3a33)\nL 3 (#120a50)\nD 7 (#6f3323)\nL 3 (#31f8c0)\nD 5 (#309583)\nR 6 (#098b52)\nU 7 (#2997d3)\nR 7 (#284152)\nU 5 (#0cf161)\nR 5 (#442342)\nD 3 (#51c983)\nR 3 (#3fd5a2)\nD 4 (#51c981)\nR 2 (#071bc2)\nD 5 (#0cf163)\nR 5 (#096492)\nD 3 (#2997d1)\nL 3 (#08aa32)\nD 5 (#617173)\nL 4 (#159f80)\nD 4 (#1ad823)\nL 2 (#189870)\nD 2 (#49cd53)\nL 7 (#542880)\nD 4 (#64a571)\nL 3 (#4c8f90)\nD 3 (#4b9403)\nL 2 (#4776a0)\nD 7 (#115af3)\nL 5 (#31f4d0)\nU 4 (#5402b3)\nL 5 (#5a5820)\nD 7 (#18b4e1)\nL 7 (#204a50)\nU 7 (#618ac1)\nL 3 (#3d4fc0)\nD 4 (#6a84b1)\nL 5 (#1db0c0)\nD 6 (#152da1)\nL 2 (#02b390)\nD 8 (#41e331)\nL 2 (#7c9b10)\nD 7 (#072371)\nL 3 (#5e3210)\nD 3 (#2aec03)\nL 2 (#7f7280)\nD 9 (#3b0d41)\nL 4 (#141b02)\nU 3 (#5d9db1)\nL 3 (#400800)\nD 7 (#132521)\nL 5 (#544ec0)\nU 7 (#25f8c3)\nL 3 (#4f24c0)\nU 2 (#25f8c1)\nL 2 (#10fca0)\nU 3 (#132523)\nR 7 (#1299b0)\nU 2 (#2375b1)\nR 6 (#25bb92)\nU 4 (#2ceb11)\nL 4 (#569262)\nU 2 (#062d81)\nL 4 (#4f0eb2)\nU 9 (#062d83)\nL 5 (#3bb532)\nU 3 (#191f21)\nL 6 (#1754a2)\nD 3 (#44d1f1)\nL 3 (#722452)\nD 4 (#394421)\nR 6 (#27a0a2)\nD 8 (#7f3ae1)\nL 6 (#1a2952)\nD 7 (#402a41)\nL 6 (#1a2950)\nD 6 (#50f3c1)\nL 5 (#5479e2)\nU 4 (#4bd6b3)\nL 4 (#435e92)\nU 2 (#388f83)\nL 3 (#43caa0)\nU 5 (#43b4a3)\nL 7 (#43caa2)\nU 7 (#1c0eb3)\nL 7 (#435e90)\nU 3 (#0033b3)\nL 4 (#35a562)\nU 5 (#2bfbb3)\nL 2 (#4ab672)\nU 8 (#6bac11)\nL 3 (#029fe2)\nU 9 (#3e0f71)\nR 4 (#50a132)\nU 7 (#3698a1)\nR 2 (#15add2)\nU 3 (#7e3841)\nR 10 (#327a12)\nU 3 (#24b1b1)\nR 8 (#2b6592)\nU 3 (#3b80a1)\nR 6 (#106112)\nU 3 (#315b31)\nL 10 (#6510e2)\nD 3 (#1e5881)\nL 3 (#3a2e42)\nU 6 (#1e5883)\nL 4 (#175ed2)\nU 4 (#0bc683)\nL 2 (#443860)\nU 3 (#5b6113)\nL 6 (#443862)\nD 7 (#3fcbf3)\nL 6 (#427de2)\nU 8 (#04e613)\nL 3 (#3a06a2)\nD 4 (#3e7273)\nL 2 (#42fd42)\nD 10 (#2579c3)\nL 3 (#234762)\nD 3 (#7dc451)\nR 4 (#33cf70)\nD 8 (#121911)\nL 4 (#8121b0)\nD 3 (#1a2d31)\nL 6 (#1831c2)\nD 2 (#1ea1b1)\nL 4 (#0674f2)\nD 3 (#1679e1)\nL 10 (#5948b2)\nD 2 (#1679e3)\nL 2 (#2f4d52)\nD 4 (#0469b1)\nL 6 (#0db472)\nD 5 (#5a0e01)\nR 6 (#471a90)\nD 4 (#101dc1)\nR 2 (#5f57e0)\nD 3 (#432761)\nR 4 (#1e6d70)\nD 3 (#576d71)\nR 2 (#306cd0)\nD 2 (#0a9a11)\nR 7 (#41d3c0)\nU 2 (#2d1fd1)\nR 3 (#51e040)\nU 3 (#2d1fd3)\nR 3 (#13c380)\nD 2 (#0a9a13)\nR 5 (#6b9900)\nD 5 (#390be1)\nL 4 (#14f860)\nD 5 (#0e3a31)\nL 6 (#5f2292)\nD 4 (#498ae1)\nL 3 (#1b53a2)\nD 6 (#22b6b1)\nL 7 (#255972)\nD 3 (#7f2ad1)\nL 4 (#1badc0)\nD 4 (#2d96e1)\nL 8 (#083460)\nD 5 (#5aa4f1)\nL 2 (#083462)\nD 4 (#07c271)\nL 2 (#1badc2)\nD 9 (#19fe01)\nL 2 (#27c492)\nD 6 (#40be73)\nL 6 (#06eee2)\nU 2 (#231bd3)\nL 3 (#3b1db2)\nU 10 (#184ae1)\nL 2 (#3cea12)\nU 6 (#4b8f61)\nL 5 (#244e82)\nU 4 (#5576d1)\nR 5 (#2e7552)\nU 6 (#372b41)\nL 5 (#0cabb0)\nD 2 (#34bde1)\nL 3 (#3288b0)\nD 5 (#82d1c3)\nL 2 (#2911e0)\nD 3 (#82d1c1)\nL 6 (#3b28a0)\nD 4 (#34bde3)\nL 3 (#561020)\nD 6 (#568d21)\nL 5 (#5f06b2)\nU 6 (#106891)\nL 6 (#0c22c2)\nU 7 (#4941b1)\nL 3 (#603862)\nU 3 (#181fe1)\nL 6 (#195962)\nU 3 (#461091)\nL 4 (#257782)\nU 5 (#7fed61)\nL 6 (#2cf8d2)\nU 6 (#042361)\nL 4 (#527050)\nU 5 (#4a5051)\nR 6 (#195960)\nU 5 (#4107a1)\nR 2 (#319d92)\nU 7 (#3f0e61)\nL 7 (#17a5c2)\nU 4 (#429851)\nL 5 (#37f9a2)\nU 4 (#436d11)\nL 5 (#25c582)\nU 3 (#436d13)\nL 3 (#3815d2)\nU 5 (#042663)\nR 4 (#00be52)\nU 3 (#5e13a3)\nR 4 (#028f62)\nD 5 (#004c43)\nR 7 (#52e262)\nU 5 (#4826b3)\nR 5 (#04ba12)\nU 3 (#4826b1)\nL 8 (#509a02)\nU 6 (#254c03)\nR 8 (#11bfc2)\nU 4 (#1fba13)\nR 5 (#5e3280)\nU 5 (#56c073)\nR 3 (#08d9c0)\nU 3 (#75e7a3)\nR 4 (#380520)\nU 4 (#651443)\nL 6 (#1d7430)\nU 7 (#15f733)\nL 2 (#4d63a2)\nU 5 (#1a8ba3)\nL 5 (#39b4c2)\nU 4 (#372fc3)\nL 2 (#11a2a2)\nU 4 (#372fc1)\nL 7 (#440a92)\nD 4 (#2e18b3)\nL 4 (#2361b2)\nD 4 (#25f413)\nL 4 (#490582)\nU 4 (#5ea151)\nL 6 (#37b702)\nU 3 (#5ea153)\nL 3 (#1e0e42)\nU 3 (#3e17d3)\nL 6 (#4b6ec0)\nU 4 (#058e11)\nL 9 (#3c5900)\nU 2 (#058e13)\nL 3 (#3a64b0)\nU 6 (#362123)\nL 4 (#7a3390)\nU 5 (#0c9e53)\nL 7 (#06a9f0)\nU 7 (#036323)\nL 5 (#0e8470)\nU 3 (#0ad513)\nL 2 (#3331c2)\nU 7 (#12fed3)\nL 5 (#3c4a52)\nU 6 (#55aa33)\nL 4 (#18e540)\nD 6 (#2984c3)\nL 4 (#18e542)\nU 3 (#49aa53)\nL 3 (#0879e2)\nU 5 (#381dc3)\nL 3 (#3c9e92)\nU 6 (#471eb1)\nL 4 (#643aa2)\nU 6 (#471eb3)\nL 4 (#148512)\nU 9 (#228b33)\nL 2 (#084e12)\nU 5 (#228f33)\nL 3 (#60a742)\nD 7 (#44a213)\nL 2 (#094262)\nD 7 (#04aee3)\nL 4 (#46a752)\nU 5 (#0dd833)\nL 3 (#533952)\nU 9 (#447da3)\nL 2 (#5e0780)\nU 3 (#2d1783)\nL 4 (#275f90)\nU 6 (#35bc53)\nL 3 (#3c9da2)\nU 4 (#22fd93)\nL 4 (#48c972)\nD 5 (#1feb43)\nL 2 (#36bf42)\nD 7 (#405583)\nL 3 (#41af42)\nU 9 (#469c81)\nL 2 (#393e22)\nU 3 (#3cd9f1)\nL 6 (#3bb442)\nD 7 (#025261)\nL 7 (#5b7290)\nU 7 (#5b1311)\nL 4 (#197fd0)\nU 2 (#49b3e1)\nL 4 (#6d2722)\nU 4 (#0dd831)\nL 4 (#4b7072)\nD 3 (#4f78c3)\nL 3 (#125ab2)\nD 6 (#4dd6b3)\nL 4 (#14b212)\nU 2 (#3db733)\nL 2 (#5bb722)\nU 7 (#519d13)\nL 3 (#2baf82)\nD 4 (#5394b3)\nL 4 (#6e6f42)\nU 8 (#316c33)\n"
}

module RealImpl = Impl<realInput/0>;

select 1
