; ModuleID = '/Users/taeyoungkim/metalift/custom_test/while3.ll'
source_filename = "/Users/taeyoungkim/metalift/custom_test/while3.c"
target datalayout = "e-m:o-i64:64-i128:128-n32:64-S128"
target triple = "arm64-apple-macosx15.0.0"

; Function Attrs: noinline nounwind optnone ssp uwtable
define dso_local i32 @test() #0 {
entry:
  %x = alloca i32, align 4
  %y = alloca i32, align 4
  store i32 0, i32* %x, align 4
  store i32 1, i32* %y, align 4
  br label %while.cond

while.cond:                                       ; preds = %while.body, %entry
  %i = load i32, i32* %y, align 4
  %cmp = icmp slt i32 %i, 3
  br i1 %cmp, label %while.body, label %while.end

while.body:                                       ; preds = %while.cond
  %i1 = load i32, i32* %x, align 4
  %i2 = load i32, i32* %y, align 4
  %add = add nsw i32 %i1, %i2
  store i32 %add, i32* %x, align 4
  %i3 = load i32, i32* %y, align 4
  %add1 = add nsw i32 %i3, 1
  store i32 %add1, i32* %y, align 4
  br label %while.cond, !llvm.loop !7

while.end:                                        ; preds = %while.cond
  %i4 = load i32, i32* %x, align 4
  ret i32 %i4
}

attributes #0 = { noinline nounwind optnone ssp uwtable "disable-tail-calls"="false" "frame-pointer"="non-leaf" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="apple-a12" "target-features"="+aes,+crc,+crypto,+fp-armv8,+fullfp16,+lse,+neon,+ras,+rcpc,+rdm,+sha2,+v8.3a,+zcm,+zcz" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.module.flags = !{!0, !1, !2, !3, !4, !5}
!llvm.ident = !{!6}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 1, !"branch-target-enforcement", i32 0}
!2 = !{i32 1, !"sign-return-address", i32 0}
!3 = !{i32 1, !"sign-return-address-all", i32 0}
!4 = !{i32 1, !"sign-return-address-with-bkey", i32 0}
!5 = !{i32 7, !"PIC Level", i32 2}
!6 = !{!"Homebrew clang version 12.0.1"}
!7 = distinct !{!7, !8}
!8 = !{!"llvm.loop.mustprogress"}
