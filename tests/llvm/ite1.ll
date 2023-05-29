; ModuleID = 'ite1.ll'
source_filename = "ite1.c"
target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx11.0.0"

; Function Attrs: noinline nounwind optnone ssp uwtable
define i32 @test(i32 %arg) #0 {
bb:
  %i = alloca i32, align 4
  %i1 = alloca i32, align 4
  store i32 %arg, i32* %i, align 4
  %i2 = load i32, i32* %i, align 4
  %i3 = icmp sgt i32 %i2, 10
  br i1 %i3, label %bb8, label %bb9

bb4:                                              ; preds = %bb8
  store i32 1, i32* %i1, align 4
  br label %bb6

bb5:                                              ; preds = %bb9
  store i32 2, i32* %i1, align 4
  br label %bb6

bb6:                                              ; preds = %bb5, %bb4
  %i7 = load i32, i32* %i1, align 4
  ret i32 %i7

bb8:                                              ; preds = %bb
  br label %bb4

bb9:                                              ; preds = %bb
  br label %bb5
}

attributes #0 = { noinline nounwind optnone ssp uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.module.flags = !{!0, !1, !2}
!llvm.ident = !{!3}

!0 = !{i32 2, !"SDK Version", [2 x i32] [i32 11, i32 3]}
!1 = !{i32 1, !"wchar_size", i32 4}
!2 = !{i32 7, !"PIC Level", i32 2}
!3 = !{!"Homebrew clang version 11.1.0"}
