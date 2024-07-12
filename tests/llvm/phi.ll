; ModuleID = 'phi.ll'
source_filename = "phi.c"
target datalayout = "e-m:o-i64:64-i128:128-n32:64-S128"
target triple = "arm64-apple-macosx11.0.0"

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define void @test(i32 %r, i32 %y) #0 {
entry:
  %r.addr = alloca i32, align 4
  %y.addr = alloca i32, align 4
  %l = alloca i32, align 4
  store i32 %r, i32* %r.addr, align 4
  store i32 %y, i32* %y.addr, align 4
  %i = load i32, i32* %y.addr, align 4
  %add = add i32 1, %i
  %tobool = icmp ne i32 %add, 0
  br i1 %tobool, label %lor.end, label %lor.rhs

lor.rhs:                                          ; preds = %entry
  %i1 = load i32, i32* %r.addr, align 4
  %add1 = add i32 2, %i1
  %tobool2 = icmp ne i32 %add1, 0
  br label %lor.end

lor.end:                                          ; preds = %lor.rhs, %entry
  %i2 = phi i1 [ true, %entry ], [ %tobool2, %lor.rhs ]
  %lor.ext = zext i1 %i2 to i32
  store i32 %lor.ext, i32* %l, align 4
  ret void
}

attributes #0 = { noinline nounwind optnone sspstrong uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="non-leaf" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="4" "target-cpu"="apple-a13" "target-features"="+aes,+crc,+crypto,+fullfp16,+lse,+neon,+ras,+rcpc,+rdm,+sha2,+v8.3a,+zcm,+zcz" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.module.flags = !{!0, !1}
!llvm.ident = !{!2}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 7, !"PIC Level", i32 2}
!2 = !{!"clang version 11.1.0"}
