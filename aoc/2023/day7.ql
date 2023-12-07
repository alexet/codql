import lib

module Impl<inStr/0 input> {
  import Helpers<input/0>

  string hand(int n) { result = lines(n).splitAt(" ", 0) }

  string card(int n, int k) { result = hand(n).charAt(k) }

  int cardCounts(int n, string card) { result = strictcount(int k | card(n, k) = card) }

  import predicates

  module RankHands<pred/0 hasJokers> {
    int cardCountsNonJ(int n, string card) {
      result = cardCounts(n, card) and
      (hasJokers() implies card != "J")
    }

    int jokers(int n) {
      if hasJokers()
      then
        result = cardCounts(n, "J")
        or
        not exists(cardCounts(n, "J")) and result = 0 and exists(hand(n))
      else (
        result = 0 and exists(hand(n))
      )
    }

    int cardKinds(int n) {
      exists(hand(n)) and
      result = count(string card | cardCountsNonJ(n, card) != 0)
    }
    
    int maxCount(int n) { result = max(cardCountsNonJ(n, _) + jokers(n)) }

    predicate is5Kind(int n) { cardKinds(n) in [0, 1] }

    predicate is4Kind(int n) {
      cardKinds(n) = 2 and
      maxCount(n) = 4
    }

    predicate isFullHouse(int n) {
      maxCount(n) = 3 and
      cardKinds(n) = 2
    }

    predicate is3Kind(int n) {
      cardKinds(n) = 3 and
      // Some card that makes 3
      maxCount(n) = 3
    }

    predicate is2Pair(int n) {
      maxCount(n) = 2 and
      cardKinds(n) = 3
    }

    predicate isPair(int n) { cardKinds(n) = 4 }

    predicate isHigh(int n) { cardKinds(n) = 5 }

    int typeRank(int n) {
      is5Kind(n) and result = 0
      or
      is4Kind(n) and result = 1
      or
      isFullHouse(n) and result = 2
      or
      is3Kind(n) and result = 3
      or
      is2Pair(n) and result = 4
      or
      isPair(n) and result = 5
      or
      isHigh(n) and result = 6
    }

    int cardRank(string s) {
      result = [2 .. 9] and
      s = result.toString()
      or
      s = "T" and result = 10
      or
      s = "J" and
      if hasJokers() then result = 1 else result = 11
      or
      s = "Q" and result = 12
      or
      s = "K" and result = 13
      or
      s = "A" and result = 14
    }

    int handRank(int n2) {
      n2 =
        rank[result](int n |
          exists(hand(n))
        |
          n
          order by
            typeRank(n) desc, cardRank(card(n, 0)), cardRank(card(n, 1)), cardRank(card(n, 2)),
            cardRank(card(n, 3)), cardRank(card(n, 4))
        )
    }

    int winnings() { result = sum(int n | exists(hand(n)) | bid(n) * handRank(n)) }
  }

  module RankP1 = RankHands<falsePred/0>;

  module RankP2 = RankHands<truePred/0>;

  int bid(int n) { result = lines(n).splitAt(" ", 1).toInt() }

  predicate winningsP1 = RankP1::winnings/0;

  predicate winningsP2 = RankP2::winnings/0;
}

string testInput() { result = "32T3K 765\nT55J5 684\nKK677 28\nKTJJT 220\nQQQJA 483\n" }

string realInput() {
  result =
    "AJ44J 454\n33848 56\n66366 699\nKQKJK 718\n47767 78\nT723K 40\nJQAKT 799\n3JQ34 871\n54622 625\n34634 602\n7K784 909\nT4T4T 379\nQQQQJ 387\nJ2J79 991\n8AT8T 310\n55KKK 705\n88JQQ 949\n83Q52 74\nJ7J7T 272\n973JK 832\nA5555 520\nQ868Q 918\nQ3AQ7 843\nK73KJ 87\nTK5KK 595\nTAAAK 102\n2AQTT 882\nTJ5T5 889\nTT23T 356\nA9749 248\n39TJ9 585\nK6242 312\n444K4 627\n5J55Q 279\n6K6T6 381\nKAJ36 105\n7J388 902\n444QQ 150\n7A7Q7 953\n57333 331\nAATAA 580\n575J5 393\n52545 910\n629KJ 749\n47A74 643\nJ9JJ9 435\n2K2K9 189\nJ33J2 600\nQ2926 598\nQ67TA 858\nA8533 193\n6Q6KQ 363\n54444 925\n7327K 552\n4A3K8 833\nJKTQ2 790\n477Q7 358\n66A6T 204\n44924 337\n4J262 807\nJJ366 676\n56555 60\n97J77 130\n8Q4KQ 729\n852Q5 934\n9KT48 133\n29TQ4 565\nQ47T2 399\n9J944 398\n2Q792 795\n7K897 804\n577J7 525\n5QQ5J 495\nQQQ92 913\n22272 291\n8Q8Q8 16\n3KKK9 258\nQ47A7 586\n76777 427\nT8J34 874\nQ5999 782\nJJ29T 173\n88837 241\n22662 300\n44K72 196\nJAAQ6 229\n94J9Q 690\nT477T 845\n3T82J 433\n43424 865\n63668 821\nT2T2T 472\n8A66Q 835\n4KKJ7 952\nT4TTQ 584\n77989 257\n37JA7 148\n78944 717\n7AJ6Q 851\n6KJQ2 122\n386A3 53\n87777 416\nKKJJT 480\n4639J 846\n9T473 695\n88K8J 632\n443A4 928\n79767 611\n84448 680\nQ258T 748\nTKTTT 249\nKKK4K 893\n36655 653\n6QAJJ 185\n5JA3Q 255\nTTJTT 190\n37QKK 432\n8Q322 691\nJ7724 548\n4T4TJ 121\n23559 134\nTT999 385\nJ2J94 765\nAA5A5 593\n33J35 683\nJ858Q 754\n99259 798\nTT45K 499\nKKKJ7 415\n2A59T 411\nK474Q 607\nAQ7T2 559\n683KT 323\nQ2T2Q 147\n33442 299\nK999K 83\n9Q2J2 988\n2J727 658\nK544J 523\nQ286T 954\nQ8K5J 794\n38AA3 1000\nA7777 360\n7QK77 808\n22226 671\nA6Q83 240\nKK6J6 225\nKKK33 776\n3JK33 52\n5T5A9 933\n2A85J 45\n5TTT5 932\n467Q4 430\nA76AT 886\n8KKKK 597\n9JJKA 389\n5K555 202\n39QQ9 604\n2A25A 487\n22Q42 43\n3333K 269\nT82TA 135\n6JAK6 741\n72Q2Q 582\nQJ49K 722\n89J6A 761\nTJKA8 517\n7979A 309\n4KQK2 278\nA5T3T 519\nA4T2Q 167\n8645A 726\nT8T8T 29\n4J4JQ 512\nKJQJQ 661\n4AA44 30\n6A666 752\n5AA92 969\nQ9QJQ 891\n674QA 549\n93Q34 96\n5QQQQ 191\n8A8A4 662\n2AQQQ 986\n66JJ6 445\n585J5 99\nTQKKT 448\nTTTJJ 569\nT8T96 620\n28622 431\nK9365 697\nQK4K4 20\nTJJJT 887\n59999 453\nJKAAA 324\n7774K 364\nJ5J2K 345\n7474J 938\n58QJ4 496\n34434 235\n55J5J 853\nQ66AQ 205\n3Q434 188\nQ43QJ 879\nKK3KA 974\n5A5Q5 811\nQQAQQ 818\n666QA 371\n55Q55 290\nT8JJ3 989\n69T32 10\n246Q3 276\nKAJA5 88\n9JJ32 641\nT8TTT 84\n333JQ 372\nKKKK2 442\n3AAJ9 735\n22K2K 572\n77377 209\n2Q683 684\n75562 380\n449A8 171\n4T5J4 386\nJ8JJJ 929\n443T4 115\nAAQ74 461\n2272J 212\n576A8 757\n64KA7 665\nA4845 815\nJTA68 316\nTQAJ6 922\n88J4Q 463\nQQ442 305\n3JJ33 119\nTTAJJ 75\n22TT2 714\nT55KT 672\nK23AQ 5\n552J5 198\n4A2J7 73\nTA89A 787\nA3K5K 82\n74Q53 545\nT7694 959\nA6JJ6 476\nAAAA6 353\nAJ9T6 923\n793J7 319\n29K46 860\n26494 464\n64654 743\n88877 265\n4AJA6 473\n77K87 981\n6QAJ3 994\n9T224 737\n77577 446\nT5QKJ 344\n4547J 840\n222J3 101\n6Q666 468\nKAT25 315\n97898 616\n22443 114\n63366 280\n89955 426\n32333 963\nA3A43 311\nA3A3J 899\n777J7 702\n9Q8K8 266\n33J39 156\nQ3KKJ 820\n8J53T 971\nJ455K 890\n88AAA 727\n555JT 677\nK88KK 253\nT2A82 977\nJ65JT 775\n5852J 459\n77585 716\nQ43K5 970\nJQATQ 37\nJ9928 3\n445T4 812\n24242 961\n66868 878\n9A4QK 26\n444T6 285\n23438 317\nT3563 111\n8T85K 72\nAQJJ2 848\nT3887 65\nJ4729 162\n2J422 687\n66266 187\n75577 304\n9562T 542\n7T5T4 136\n7AKKK 655\nK2357 200\nT2A25 915\n84666 250\n73338 439\n66699 262\nKT7T7 199\nJJ325 751\n222AT 103\nT8TT2 738\n8858A 182\n2J842 314\n42TQJ 57\n7QQ33 141\n4449T 785\n35998 436\nK236A 184\n887J7 286\n5A972 139\n266A6 674\n3ATK7 861\nT76AT 340\n4AT44 721\n5J225 455\n382Q9 68\nQT9K2 298\n29979 259\nKA66A 896\nT5TAT 888\nK94T4 404\n54KT6 254\n2878T 599\nAAA4A 366\nA47A7 227\nJ4242 100\n33QA9 62\n99799 995\n55437 228\nAQAAA 382\nKAKKA 79\n44344 71\n72627 652\nTTTAT 231\n666AA 438\nTJTKJ 405\nQ2TJT 962\n65A88 281\nJ5Q75 931\n22444 852\n3JKJK 38\nKQKQK 872\n6Q4Q8 339\n444QJ 85\nQJ545 732\n95KKK 646\n88878 284\n4A7J4 470\n9A39A 127\n892QJ 203\n47748 332\nQ79QQ 425\n37Q33 803\n7K4T2 828\nQQQ4Q 719\nKKKAK 973\n2JJ66 54\n48884 69\n88J6J 917\n9K9KK 532\nTAJJ3 758\n7K9KK 651\nJ6Q2J 956\nAA388 725\n62J72 826\n24222 965\n69699 274\n767KK 175\n9A67J 779\n26K55 329\nK4K94 107\n49444 696\nA6T8K 685\n872J8 908\n49845 628\n34473 578\n25673 334\n3A3A5 287\n7TTTT 335\n9K32T 403\nQ3A3Q 330\nT4QA5 306\nQTTK9 784\n989J9 6\nTTT77 159\nA9Q46 490\n9Q442 177\nJAAAJ 789\n444J4 407\n35555 244\nAAAA5 842\nT55T5 308\nKKTKT 113\n5335J 186\n58J58 296\nQ7TJT 536\nT232J 951\nJKKJA 245\n52AK6 619\n63336 21\n7K777 759\n4T9KK 58\n2552T 375\n2AQT3 48\nJ9AAJ 516\n46665 645\nKT84Q 575\n88K4J 946\nQQJTT 854\n99J9J 489\n99659 966\n5Q9T8 347\nQJ5J9 936\n59JTT 774\nK5J95 326\nA2ATK 95\nJK7K7 715\nAJAA4 613\nT754A 926\n7A728 979\n93T7Q 704\nQJ2K7 70\n97799 633\n5599Q 920\nT773T 144\n7J738 154\n46464 834\n959QQ 424\n56AA6 31\nQ5684 822\n8A688 35\n4J436 670\n38K33 531\n888JA 118\n3T35T 201\n7626T 384\nJ8888 689\n2QATA 160\nKKKJJ 814\n428J8 753\nTQ9JT 740\nTA9T9 338\n87A8A 660\n34493 647\n9J485 788\n56T7Q 322\nQJQ7Q 631\n44464 421\n99K2J 935\n759QT 810\nKT6QQ 503\n9KAA9 883\n97K8T 77\n72288 396\n29TJ3 608\n7Q977 452\nK36J8 343\nT9T22 443\nK7JT3 98\n3A9TJ 400\nAJAAA 251\nTTTT3 709\nAA2A2 544\n6586Q 178\n25222 805\nQ9J75 881\nA4394 484\n77T79 264\n4J4J4 862\n7JJAJ 469\n4446J 44\n252Q2 763\nAA88J 420\nT4T2T 491\nKQQKQ 447\n63888 140\n93493 213\n77977 998\n53J9K 367\nJ2324 864\n92954 374\n47J44 283\n98QJ8 493\n9AQ39 558\nA4AA4 391\n98988 797\n8QTJ6 836\n33766 560\nT6AT6 780\n96J66 824\n2T4KA 829\nA22JK 429\nK3599 104\nJ9Q96 143\nQ82Q9 964\n77474 179\nQ4K9K 711\n4A49T 320\nQA669 700\n22333 999\n3K97Q 537\nQA889 857\n595TT 792\nJ77T7 601\nK5587 945\nA7JAA 223\nT7277 868\n6TTT9 673\nAAA42 997\nKKKQK 295\nK4QQK 22\n74562 55\n77252 796\n458Q9 747\n77477 233\nT3TT3 667\n888A9 650\n5QQJA 744\n7A576 24\nJ25T9 89\n8K884 9\n65565 562\n47QQQ 639\nA4768 914\n3J9A4 554\n39T82 46\n9AK43 522\nK8K68 590\nQ2487 501\nQ8J87 968\n22A22 606\n99KKQ 543\n33533 535\n99J9Q 294\nJ262J 760\n89327 976\n7Q677 164\nATTT6 678\n7J78J 267\nKJKK2 462\nK522Q 762\n44AAK 827\n7A7TA 482\nQ9JA9 692\n4K9J4 369\n5A424 211\nK2782 34\n9KAKJ 273\n3K3JK 378\n85T37 215\nAAA37 475\nQ777Q 394\n8383A 773\nJ66J8 960\nT29AQ 905\nJQ487 642\n47444 636\n2AAJ5 876\n86886 195\n58525 221\nAK9TK 993\nJKKKK 242\n97JJ9 239\n77939 252\nT55AK 947\n73337 941\n6423K 47\n49762 944\nA458K 541\n4T755 450\n7TK48 138\n22223 583\nTKTTK 629\n5K5K5 577\n2A272 768\nQ47TA 819\n62AKA 734\nK66QK 823\n8998K 120\n22992 880\n85TTT 596\n9TA5K 710\n4K276 856\n98K88 297\nK8888 921\n32622 414\nKKK44 987\nK7J38 958\nJJ32J 524\nJKKK8 18\nQA5J4 232\n936QA 863\n55522 733\nK7A76 479\n447KJ 515\n66696 813\n89888 957\n99Q33 478\n5A264 449\n55A64 97\n83388 978\nJ5555 86\n7555T 781\n46JT8 206\nJ4448 859\n4J777 388\n55955 208\nT99AA 793\n2835A 869\n6559J 617\nQQQQ3 157\nQ3AAA 919\n6T73A 63\n49KKA 333\n6A92T 528\n48J24 373\nQQJ8Q 256\n3QQ7Q 707\n7QQQQ 11\n42T79 126\n35434 477\n9QQ99 712\n5K2QQ 603\n595T5 110\nQT6TQ 618\nQ6Q76 570\nJ8979 219\nTT66T 207\n2T682 131\nJQQQJ 992\nQJ44Q 940\nQ473Q 28\nQQQ99 588\n37768 197\nQKKKT 328\n77J99 589\n93999 563\nA77AA 362\nKK7K6 996\n22255 579\n94944 730\n3495T 897\nQTTQT 539\n96AJ9 529\nA2224 703\n62659 377\n7KTJT 486\nT786Q 573\n6JA6A 214\nKAA9J 50\n4488T 538\nT2T88 485\n22Q2Q 67\n3K7K8 605\n75JQ7 498\n3T3J5 288\n8679T 27\n7TQ52 483\nQQ87A 365\nQKKKA 392\nJK99K 505\nJQQQ3 825\nK4Q49 155\nJ76Q8 770\nTJ8J5 94\n3433T 982\n34AA4 506\n72877 137\n42836 801\nJQQQT 440\n59955 688\n8K48K 855\nQ8KA5 756\n974JJ 675\n53545 530\n56844 783\n333J3 441\n93JQ6 767\n5TTTT 318\n257T9 533\nQA6A6 8\n8A298 937\n29KT8 870\nA8A8K 955\n33QT3 841\n5QKJ7 939\nK2568 183\nA9JJ9 720\nJA8AA 948\n9A989 180\n88J8J 236\n8TT55 571\nATATA 527\n4K266 451\nQ6644 701\n44KK4 850\n86863 830\n5QT36 930\nA4A6A 346\nK3KTT 36\n29JJ2 351\nAJKQJ 307\n3975K 166\nT3K3J 844\nA334J 806\n5K348 885\n4A2Q4 875\n666T6 566\nA7Q9A 419\nA948Q 630\nTJ222 666\nKTKJ5 907\n3343J 849\n77282 169\n9J99K 975\nT8444 634\n9KJTK 510\n54449 124\n2857T 418\nJ8T88 508\nKKKK3 243\n6425J 728\nK3TQQ 152\n6666J 390\n59599 906\n576J8 739\n8838J 903\n6Q6QQ 194\nKQ366 23\nQQ38Q 927\n3KJ38 151\n33Q9J 866\n8884A 507\nJ8K23 513\nA82Q7 370\n2Q424 990\n73Q5J 224\n5JQJA 123\n845Q8 912\n7893A 376\nJ7847 838\nKK442 594\nQ2K9A 397\nQQJ4Q 694\n44J3J 624\n72A34 444\n59678 663\n88T88 341\n7AJ33 234\nK5J5J 321\nT94TQ 13\n49Q5K 547\n44T24 967\n9629K 128\n69T88 980\n6T36T 576\n252K2 168\n29797 492\n9372J 474\nT8AAA 325\n89TT8 402\nJJT78 904\nKAJ46 567\n9TT49 521\nK9599 59\n28222 361\n7895A 357\n95A59 90\n4888J 91\nQ9J3T 230\n72777 268\n62A57 327\nJJJJJ 406\n7TJ43 984\n47944 237\n93396 222\n554KK 706\n574K7 574\n6AT86 129\nJ2T2T 467\n888Q8 437\nQQTQQ 755\nKKK5K 466\nJ9KJK 80\nKJ2K9 557\nK5KK2 422\n5J434 681\n99J99 19\n54779 293\n48K76 226\n33343 561\n5T787 149\nQ942K 401\n858J8 911\n9KTQ9 410\nKT3K2 943\n29T98 731\n7KKK7 898\nA6K66 772\n78273 277\n777Q7 693\n2J2J2 354\nJAK97 4\n6T64T 713\nT65Q2 174\nJ2T2Q 270\n48348 481\n5J66A 153\n56828 109\nJQ457 540\n6Q6Q6 12\n68J86 146\n7433J 41\nQA6A8 657\nTT2TT 336\nK89Q6 555\nA7T38 591\n8A562 383\nTT7T4 546\nJ4443 117\n6J636 142\n4KJ4J 686\n27767 494\nA99J9 301\nKQQJ5 750\n8TA88 839\n72277 15\nTA568 7\n25QT4 564\nAJ4J3 2\nA33K3 644\nT3QK6 847\n375AJ 172\n799J9 640\n86TT8 395\n44JK6 669\n2KKKQ 218\nKK344 51\n33TTJ 514\nTTAA4 502\n53252 664\n737KK 412\n66KT9 260\n44469 355\nT6A2J 458\nJ587Q 679\n6J226 42\n75TKA 216\nT88K8 610\nAT4A2 413\n9JA42 587\n33Q2T 556\n56666 682\n4T44T 766\n52Q29 408\n4T28A 33\nJ3366 409\n62J9J 497\nJAA8Q 892\nTT733 622\nTA5JT 916\n22277 488\n3A3A3 626\nQ98J6 428\nKJK58 1\n3Q392 465\nJJ466 942\nATTTA 659\n82248 698\nQ9A83 368\n6556T 553\nJA8AJ 92\n7A54A 192\n2QQ82 302\n86666 509\nA5J42 263\nT8J8K 742\nAJ6T4 950\n5K544 348\n76359 210\n689J4 983\n37333 342\nJ2222 275\n88848 900\nA9TJT 895\n8JK46 238\n75457 247\nQ29A2 568\n79797 158\n44T44 526\n242JQ 924\n22292 163\nKAA6A 434\nQJ9A2 417\n633J5 39\nJ777J 668\n86239 64\n69993 61\n226JK 791\nJ762K 350\nJ66A6 723\nT5JJJ 116\n33363 303\nA2AJA 132\n9988Q 786\n8TK6K 14\n57734 837\nJ6AAA 349\n44J4A 456\nKK855 777\nK8662 901\n6JK8A 282\n59575 550\nQQQ6Q 612\nT9KT9 985\nQTT7T 66\n95533 145\n22794 771\n5TAA7 17\n4K354 621\n7KKKK 635\nK5A44 638\nT9353 500\n6926J 313\nJ9Q35 125\n222JK 746\nQ2QJ2 769\n4A8JT 217\n97775 649\n6KAK5 165\nQ7T67 614\nTK8QT 724\n2AJ23 809\n3TTTA 518\nKJ996 176\n88588 802\nK855A 623\nQ7QQ7 581\nT9AJ5 359\nJ4JJ5 867\n56656 32\n54566 884\n4K5K4 708\nQ5766 778\n9867A 292\n79888 592\nK6Q25 220\n644J6 654\nQ78TK 161\nAAAA8 877\nJJTT6 112\nT3ATA 261\n33AAA 106\n99494 81\n99989 551\n96TJ9 170\n85J8A 181\n79647 25\n3K57Q 289\nT5888 816\n986Q5 471\nKK6KK 504\n3J8Q3 108\n3A37A 764\nJK5KK 76\n2T2JA 423\nAQQ6A 831\n82228 534\nT9TTT 93\n942A2 648\nK7Q89 637\n35535 457\n43KJJ 873\n53A84 460\nQ85K8 352\nQTKTT 745\n36893 49\n2J99J 609\n43K78 271\nK3456 736\nJQ462 894\n6JQJQ 511\n8J6K5 246\n2Q777 972\nJ876T 800\nQ5JQQ 656\nJJAJT 817\n9T6T9 615"
}

module TestImpl = Impl<testInput/0>;

module RealImpl = Impl<realInput/0>;

select RealImpl::winningsP1(), RealImpl::winningsP2()
