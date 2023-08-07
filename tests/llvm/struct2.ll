; ModuleID = 'struct2.ll'
source_filename = "struct2.c"
target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx12.0.0"

%struct.Test = type { i32, i32, i32, i32, i32, i32 }

; Function Attrs: noinline nounwind optnone ssp uwtable
define i32 @ML_Test_get_field1(%struct.Test* %arg) #0 {
bb:
  %i = alloca %struct.Test*, align 8
  store %struct.Test* %arg, %struct.Test** %i, align 8
  %i1 = load %struct.Test*, %struct.Test** %i, align 8
  %i2 = getelementptr inbounds %struct.Test, %struct.Test* %i1, i32 0, i32 0
  %i3 = load i32, i32* %i2, align 4
  ret i32 %i3
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define void @ML_Test_set_field1(%struct.Test* %arg, i32 %arg1) #0 {
bb:
  %i = alloca %struct.Test*, align 8
  %i2 = alloca i32, align 4
  store %struct.Test* %arg, %struct.Test** %i, align 8
  store i32 %arg1, i32* %i2, align 4
  %i3 = load i32, i32* %i2, align 4
  %i4 = load %struct.Test*, %struct.Test** %i, align 8
  %i5 = getelementptr inbounds %struct.Test, %struct.Test* %i4, i32 0, i32 0
  store i32 %i3, i32* %i5, align 4
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define i32 @ML_Test_get_field2(%struct.Test* %arg) #0 {
bb:
  %i = alloca %struct.Test*, align 8
  store %struct.Test* %arg, %struct.Test** %i, align 8
  %i1 = load %struct.Test*, %struct.Test** %i, align 8
  %i2 = getelementptr inbounds %struct.Test, %struct.Test* %i1, i32 0, i32 1
  %i3 = load i32, i32* %i2, align 4
  ret i32 %i3
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define void @ML_Test_set_field2(%struct.Test* %arg, i32 %arg1) #0 {
bb:
  %i = alloca %struct.Test*, align 8
  %i2 = alloca i32, align 4
  store %struct.Test* %arg, %struct.Test** %i, align 8
  store i32 %arg1, i32* %i2, align 4
  %i3 = load i32, i32* %i2, align 4
  %i4 = load %struct.Test*, %struct.Test** %i, align 8
  %i5 = getelementptr inbounds %struct.Test, %struct.Test* %i4, i32 0, i32 1
  store i32 %i3, i32* %i5, align 4
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define void @test(%struct.Test* noalias sret align 4 %arg, i32 %arg1, i32 %arg2) #0 {
bb:
  %i = alloca i32, align 4
  %i3 = alloca i32, align 4
  store i32 %arg1, i32* %i, align 4
  store i32 %arg2, i32* %i3, align 4
  %i4 = load i32, i32* %i, align 4
  call void @ML_Test_set_field1(%struct.Test* %arg, i32 %i4)
  %i5 = load i32, i32* %i3, align 4
  call void @ML_Test_set_field2(%struct.Test* %arg, i32 %i5)
  ret void
}

attributes #0 = { noinline nounwind optnone ssp uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.module.flags = !{!0, !1}
!llvm.ident = !{!2}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 7, !"PIC Level", i32 2}
!2 = !{!"Homebrew clang version 11.1.0"}
