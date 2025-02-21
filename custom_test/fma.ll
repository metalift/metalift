; ModuleID = '/Users/taeyoungkim/metalift/custom_test/fma.ll'
source_filename = "/Users/taeyoungkim/metalift/custom_test/fma.c"
target datalayout = "e-m:o-i64:64-i128:128-n32:64-S128"
target triple = "arm64-apple-macosx15.0.0"

; Function Attrs: noinline nounwind optnone ssp uwtable
define dso_local i32 @test(i32 %base, i32 %arg1, i32 %base2, i32 %arg2) #0 {
entry:
  %base.addr = alloca i32, align 4
  %arg1.addr = alloca i32, align 4
  %base2.addr = alloca i32, align 4
  %arg2.addr = alloca i32, align 4
  %a = alloca i32, align 4
  store i32 %base, i32* %base.addr, align 4
  store i32 %arg1, i32* %arg1.addr, align 4
  store i32 %base2, i32* %base2.addr, align 4
  store i32 %arg2, i32* %arg2.addr, align 4
  store i32 0, i32* %a, align 4
  %i = load i32, i32* %base.addr, align 4
  %i1 = load i32, i32* %base2.addr, align 4
  %add = add nsw i32 %i, %i1
  %i2 = load i32, i32* %arg1.addr, align 4
  %i3 = load i32, i32* %arg2.addr, align 4
  %mul = mul nsw i32 %i2, %i3
  %add1 = add nsw i32 %add, %mul
  store i32 %add1, i32* %a, align 4
  %i4 = load i32, i32* %a, align 4
  %i5 = load i32, i32* %a, align 4
  %add2 = add nsw i32 %i4, %i5
  store i32 %add2, i32* %a, align 4
  %i6 = load i32, i32* %a, align 4
  ret i32 %i6
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
