; ModuleID = 'gaudi/argmax.ll'
source_filename = "gaudi/argmax.cc"
target datalayout = "e-m:o-i64:64-i128:128-n32:64-S128"
target triple = "arm64-apple-macosx11.0.0"

%"class.std::__1::vector" = type { %"class.std::__1::__vector_base" }
%"class.std::__1::__vector_base" = type { i32*, i32*, %"class.std::__1::__compressed_pair" }
%"class.std::__1::__compressed_pair" = type { %"struct.std::__1::__compressed_pair_elem" }
%"struct.std::__1::__compressed_pair_elem" = type { i32* }

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define i32 @_Z6argmaxNSt3__16vectorIiNS_9allocatorIiEEEE(%"class.std::__1::vector"* %values) #0 {
entry:
  %max_i = alloca i32, align 4
  %max_value = alloca i32, align 4
  %i = alloca i32, align 4
  store i32 0, i32* %max_i, align 4
  %call = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__16vectorIiNS_9allocatorIiEEEixEm(%"class.std::__1::vector"* %values, i64 0) #1
  %i1 = load i32, i32* %call, align 4
  store i32 %i1, i32* %max_value, align 4
  store i32 1, i32* %i, align 4
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %entry
  %i2 = load i32, i32* %i, align 4
  %conv = sext i32 %i2 to i64
  %call1 = call i64 @_ZNKSt3__16vectorIiNS_9allocatorIiEEE4sizeEv(%"class.std::__1::vector"* %values) #1
  %cmp = icmp ult i64 %conv, %call1
  br i1 %cmp, label %bb, label %bb11

for.body:                                         ; preds = %bb
  %i3 = load i32, i32* %i, align 4
  %conv2 = sext i32 %i3 to i64
  %call3 = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__16vectorIiNS_9allocatorIiEEEixEm(%"class.std::__1::vector"* %values, i64 %conv2) #1
  %i4 = load i32, i32* %call3, align 4
  %i5 = load i32, i32* %max_value, align 4
  %cmp4 = icmp sgt i32 %i4, %i5
  br i1 %cmp4, label %bb12, label %bb13

if.then:                                          ; preds = %bb12
  %i6 = load i32, i32* %i, align 4
  store i32 %i6, i32* %max_i, align 4
  %i7 = load i32, i32* %i, align 4
  %conv5 = sext i32 %i7 to i64
  %call6 = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__16vectorIiNS_9allocatorIiEEEixEm(%"class.std::__1::vector"* %values, i64 %conv5) #1
  %i8 = load i32, i32* %call6, align 4
  store i32 %i8, i32* %max_value, align 4
  br label %if.end

if.end:                                           ; preds = %bb13, %if.then
  br label %for.inc

for.inc:                                          ; preds = %if.end
  %i9 = load i32, i32* %i, align 4
  %inc = add i32 %i9, 1
  store i32 %inc, i32* %i, align 4
  br label %for.cond

for.end:                                          ; preds = %bb11
  %i10 = load i32, i32* %max_i, align 4
  ret i32 %i10

bb:                                               ; preds = %for.cond
  br label %for.body

bb11:                                             ; preds = %for.cond
  br label %for.end

bb12:                                             ; preds = %for.body
  br label %if.then

bb13:                                             ; preds = %for.body
  br label %if.end
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden nonnull align 4 dereferenceable(4) i32* @_ZNSt3__16vectorIiNS_9allocatorIiEEEixEm(%"class.std::__1::vector"* %this, i64 %__n) #0 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::vector"*, align 8
  %__n.addr = alloca i64, align 8
  store %"class.std::__1::vector"* %this, %"class.std::__1::vector"** %this.addr, align 8
  store i64 %__n, i64* %__n.addr, align 8
  %this1 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %this.addr, align 8
  %i = bitcast %"class.std::__1::vector"* %this1 to %"class.std::__1::__vector_base"*
  %__begin_ = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %i, i32 0, i32 0
  %i1 = load i32*, i32** %__begin_, align 8
  %i2 = load i64, i64* %__n.addr, align 8
  %arrayidx = getelementptr i32, i32* %i1, i64 %i2
  ret i32* %arrayidx
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden i64 @_ZNKSt3__16vectorIiNS_9allocatorIiEEE4sizeEv(%"class.std::__1::vector"* %this) #0 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::vector"*, align 8
  store %"class.std::__1::vector"* %this, %"class.std::__1::vector"** %this.addr, align 8
  %this1 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %this.addr, align 8
  %i = bitcast %"class.std::__1::vector"* %this1 to %"class.std::__1::__vector_base"*
  %__end_ = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %i, i32 0, i32 1
  %i1 = load i32*, i32** %__end_, align 8
  %i2 = bitcast %"class.std::__1::vector"* %this1 to %"class.std::__1::__vector_base"*
  %__begin_ = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %i2, i32 0, i32 0
  %i3 = load i32*, i32** %__begin_, align 8
  %sub.ptr.lhs.cast = ptrtoint i32* %i1 to i64
  %sub.ptr.rhs.cast = ptrtoint i32* %i3 to i64
  %sub.ptr.sub = sub i64 %sub.ptr.lhs.cast, %sub.ptr.rhs.cast
  %sub.ptr.div = sdiv exact i64 %sub.ptr.sub, 4
  ret i64 %sub.ptr.div
}

attributes #0 = { noinline nounwind optnone sspstrong uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="non-leaf" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="4" "target-cpu"="apple-a13" "target-features"="+aes,+crc,+crypto,+fullfp16,+lse,+neon,+ras,+rcpc,+rdm,+sha2,+v8.3a,+zcm,+zcz" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { nounwind }

!llvm.module.flags = !{!0, !1}
!llvm.ident = !{!2}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 7, !"PIC Level", i32 2}
!2 = !{!"clang version 11.1.0"}
