/*
 PHI node test. The default CFG should be:

bb:
  ...
  br i1 %tmp5, label %bb9, label %bb6

bb6:                                              ; preds = %bb
  %tmp7 = load i32, i32* %tmp, align 4
  %tmp8 = icmp ne i32 %tmp7, 0
  br label %bb9

bb9:                                              ; preds = %bb6, %bb
  %tmp10 = phi i1 [ true, %bb ], [ %tmp8, %bb6 ]

  after adding empty blocks it should look like:

bb:
  ...
  br i1 %tmp6, label %bb14, label %bb15

bb14:                                             ; preds = %bb
  br label %bb11

bb15:                                             ; preds = %bb
  br label %bb7

bb7:                                              ; preds = %bb15
  %tmp8 = load i32, i32* %tmp, align 4
  %tmp9 = add nsw i32 2, %tmp8
  %tmp10 = icmp ne i32 %tmp9, 0
  br label %bb11

bb11:                                             ; preds = %bb14, %bb7
  %tmp12 = phi i1 [ true, %bb14 ], [ %tmp10, %bb7 ]
  %tmp13 = zext i1 %tmp12 to i32
  store i32 %tmp13, i32* %tmp3, align 4
  ret void

  where bb14 and bb15 are added and the preds in bb11's phi node are updated
  */

void test (int r, int y)
{
  int l = (1+y) || (2+r);
}
