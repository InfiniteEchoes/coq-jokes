Require Import CoqJokes.CoqJokes.

(* NOTE:
INTRODUCTION.
I have randomly collected some pieces from the internet, and
below will be some very slow attempts to formalize these texts.
Since they are much more wilder to give exact meanings, I might
just delete some of the texts in no time once I find them too hard
to formalize.

The final goal for these text is not to prove that they are jokes, or
to say, they are contradictory. Something even softer to prove is that 
they can be comprehended correctly.
*)

(* ************************ *)
(* Ideas to formalize *)
(* ************************ *)

(* TODO: formalize this or delete this
我向你走了过去 你向我走了过来
我蒙上了我的双眼 你为我蒙上了你的双眼
没有内心的日子里 心像水流一般流走
身后海岸闪烁着清晨的辉煌 睡醒的人懒散地收拾衣裳
双目惺忪 迷茫而彷徨

我不愿再最新一时之爱或一时之怨
一纸过时的航帆没有乘行的必要
沉睡的人依旧沉迷于沉眠的梦
因黑色的太阳依旧闪耀着明亮的光
而这一切离我太远
而我离你太远 太远

是何样的僧侣在岸边翘首以盼
是何样的僧侣佝偻前行
他健壮的身躯被禁锢于脚下的铁钉
他露出了甜美的笑容
他任由火辣辣的太阳炙烤

看那 又一个沉醉的人
我亦仅在一条更迂回的河流上航行
向岸边传出阵阵歌唱
我亦尽在一条更阴凉的小径上行走
走向你的心灵 走向你忘却 逃离的泪雨
*)
Module Myth_1.
  Module Sentences.
    Definition s_1 := And
    (* TODO: expand further *)
      (Plain "I walked into you")
      (Plain "You walked into me").
    
    (* TODO: expand further *)
    Definition s_2 := And
      (Plain "I covered my eyes")
      (Plain "You covered your eyes for me").
  End Sentences.
End Myth_1.

(* 
为什么我要尽兴奔跑？
在那个温暖的下午
嫣红的花瓣在空中散开
洁白的石柱印染着彩霞
夜风的凉爽正徐徐地送来
白色礼服的人们正享用着晚茶
白色的别墅要举办盛大的婚礼
我却天真地跑去其中搅局
不小心踏入一家人前门内
佣人警告我不要调皮
我全然不顾 他亦漫不经心地搬运着桌子
我要泡上陡峭的沥青坡道
在那个斜坡的转角
方能栽入晕染的酒夜
沉醉于玫瑰漫天的节庆时光
*)

(* 
今天开始 我睁开了半只眼睛
看到了一片朦胧 倦意与无神
*)

(* 
心是真正的底力
无心者在混沌的现象中彷徨
*)

(* 
我听到了湖畔的风了
它再度在我耳边响起
一切都是如此地宁静
在沉稳的河畔低声吟唱
*)

(* 
谁在眺望星空
谁在星空上望着我
让我原地不动

*)

(* 
我遨游于星空之中 仰望着未来的热寂
当我重新注视眼前 你早已闭上了眼睛
*)