import Benchmark.Cases.Zodiac.RolesDecoderFaithfulness.Specs

namespace Benchmark.Cases.Zodiac.RolesDecoderFaithfulness

mutual
  theorem roles_isInlined_eq_abiStatic (t : AbiTy) :
      rolesIsInlined t = abiStatic t := by
    cases t with
    | staticWords n => simp [rolesIsInlined, abiStatic]
    | dynamicBytes => simp [rolesIsInlined, abiStatic]
    | string => simp [rolesIsInlined, abiStatic]
    | tuple xs =>
        simp [rolesIsInlined, abiStatic, roles_isInlinedList_eq_abiStaticList xs]
    | dynamicArray elem => simp [rolesIsInlined, abiStatic]
    | abiEncoded inner => simp [rolesIsInlined, abiStatic]
    | transparent child =>
        simp [rolesIsInlined, abiStatic, roles_isInlined_eq_abiStatic child]

  theorem roles_isInlinedList_eq_abiStaticList (xs : List AbiTy) :
      rolesIsInlinedList xs = abiStaticList xs := by
    cases xs with
    | nil => simp [rolesIsInlinedList, abiStaticList]
    | cons x xs =>
        simp [rolesIsInlinedList, abiStaticList,
          roles_isInlined_eq_abiStatic x,
          roles_isInlinedList_eq_abiStaticList xs]
end

mutual
  theorem roles_inlinedSize_eq_abiStaticBytes (t : AbiTy) :
      rolesInlinedSize t = abiStaticBytes t := by
    cases t with
    | staticWords n => simp [rolesInlinedSize, abiStaticBytes]
    | dynamicBytes => simp [rolesInlinedSize, abiStaticBytes]
    | string => simp [rolesInlinedSize, abiStaticBytes]
    | tuple xs =>
        simp [rolesInlinedSize, abiStaticBytes,
          roles_inlinedSizeList_eq_abiStaticBytesList xs]
    | dynamicArray elem => simp [rolesInlinedSize, abiStaticBytes]
    | abiEncoded inner => simp [rolesInlinedSize, abiStaticBytes]
    | transparent child =>
        simp [rolesInlinedSize, abiStaticBytes,
          roles_inlinedSize_eq_abiStaticBytes child]

  theorem roles_inlinedSizeList_eq_abiStaticBytesList (xs : List AbiTy) :
      rolesInlinedSizeList xs = abiStaticBytesList xs := by
    cases xs with
    | nil => simp [rolesInlinedSizeList, abiStaticBytesList]
    | cons x xs =>
        simp [rolesInlinedSizeList, abiStaticBytesList,
          roles_inlinedSize_eq_abiStaticBytes x,
          roles_inlinedSizeList_eq_abiStaticBytesList xs]
end

theorem metadata_bridge (t : AbiTy) :
    metadata_bridge_spec t := by
  constructor
  · exact roles_isInlined_eq_abiStatic t
  · intro _h
    exact roles_inlinedSize_eq_abiStaticBytes t

theorem rolesHeadEntryWidth_eq_abiHeadEntryWidth (t : AbiTy) :
    rolesHeadEntryWidth t = abiHeadEntryWidth t := by
  unfold rolesHeadEntryWidth abiHeadEntryWidth
  rw [roles_isInlined_eq_abiStatic t]
  by_cases h : abiStatic t = true
  · simp [h, roles_inlinedSize_eq_abiStaticBytes t]
  · simp [h]

theorem sumMapTake_roles_eq_abi
    (children : List AbiTy) (i : Nat) :
    sumMapTake rolesHeadEntryWidth children i =
      sumMapTake abiHeadEntryWidth children i := by
  induction children generalizing i with
  | nil =>
      cases i <;> simp [sumMapTake]
  | cons x xs ih =>
      cases i with
      | zero => simp [sumMapTake]
      | succ i =>
          simp [sumMapTake, rolesHeadEntryWidth_eq_abiHeadEntryWidth x, ih i]

theorem rolesHeadOffsetBefore_eq_abiHeadOffsetBefore
    (children : List AbiTy) (i : Nat) :
    rolesHeadOffsetBefore children i = abiHeadOffsetBefore children i :=
  sumMapTake_roles_eq_abi children i

theorem safeTailFromHead_eq_canonicalTailStart
    (data : Calldata) (location headOffset : Nat) :
    safeTailFromHead data location headOffset =
      canonicalTailStart data location headOffset := by
  unfold safeTailFromHead canonicalTailStart guardedWord nonForwardTail
  by_cases hRead : location + headOffset + wordSize <= data.len
  · have hNotLt : ¬data.len < location + headOffset + wordSize := Nat.not_lt.mpr hRead
    simp [hRead, hNotLt]
    by_cases hTail : data.wordAt (location + headOffset) ≤ headOffset
    · simp [hTail]
    · by_cases hBounds : location + data.wordAt (location + headOffset) + wordSize ≤ data.len
      · have hNotBoundsLt :
          ¬data.len < location + data.wordAt (location + headOffset) + wordSize :=
            Nat.not_lt.mpr hBounds
        simp [hTail, hBounds, hNotBoundsLt]
      · have hBoundsLt :
          data.len < location + data.wordAt (location + headOffset) + wordSize :=
            Nat.lt_of_not_ge hBounds
        simp [hTail, hBounds, hBoundsLt]
  · simp [hRead, Nat.not_le.mp hRead]

theorem rolesDynamicElementBlock_eq_refDynamicElementBlock
    (data : Calldata) (elementsBlockStart i : Nat) :
    rolesDynamicElementBlock data elementsBlockStart i =
      refDynamicElementBlock data elementsBlockStart i := by
  simp [rolesDynamicElementBlock, refDynamicElementBlock,
    safeTailFromHead_eq_canonicalTailStart]

theorem rolesChildBlock_eq_refTupleChildBlock
    (data : Calldata) (location : Nat) (children : List AbiTy) (i : Nat) :
    rolesChildBlock data location children i =
      refTupleChildBlock data location children i := by
  unfold rolesChildBlock refTupleChildBlock
  cases hChild : childAt? children i with
  | none => simp
  | some child =>
      simp [rolesHeadOffsetBefore_eq_abiHeadOffsetBefore children i,
        roles_isInlined_eq_abiStatic, safeTailFromHead_eq_canonicalTailStart]

mutual
  theorem rolesTupleTailSizesFuel_eq_refTupleTailSizesFuel
      (fuel : Nat) (data : Calldata) (blockStart headCursor : Nat)
      (children : List AbiTy) :
      rolesTupleTailSizesFuel fuel data blockStart headCursor children =
        refTupleTailSizesFuel fuel data blockStart headCursor children := by
    cases fuel with
    | zero => simp [rolesTupleTailSizesFuel, refTupleTailSizesFuel]
    | succ fuel =>
        cases children with
        | nil => simp [rolesTupleTailSizesFuel, refTupleTailSizesFuel]
        | cons child rest =>
            by_cases hStatic : abiStatic child = true
            · simp [rolesTupleTailSizesFuel, refTupleTailSizesFuel,
                rolesHeadEntryWidth_eq_abiHeadEntryWidth child,
                roles_isInlined_eq_abiStatic child, hStatic,
                rolesTupleTailSizesFuel_eq_refTupleTailSizesFuel fuel]
            · simp [rolesTupleTailSizesFuel, refTupleTailSizesFuel,
                rolesHeadEntryWidth_eq_abiHeadEntryWidth child,
                roles_isInlined_eq_abiStatic child, hStatic,
                safeTailFromHead_eq_canonicalTailStart,
                rolesTupleTailSizesFuel_eq_refTupleTailSizesFuel fuel,
                rolesEncodedSizeFuel_eq_refEncodedSizeFuel fuel]

  theorem rolesArrayElementSizesFuel_eq_refArrayElementSizesFuel
      (fuel : Nat) (data : Calldata) (elementsBlockStart : Nat)
      (elem : AbiTy) (i count : Nat) :
      rolesArrayElementSizesFuel fuel data elementsBlockStart elem i count =
        refArrayElementSizesFuel fuel data elementsBlockStart elem i count := by
    cases fuel with
    | zero => simp [rolesArrayElementSizesFuel, refArrayElementSizesFuel]
    | succ fuel =>
        by_cases hi : i < count
        · by_cases hStatic : abiStatic elem = true
          · simp [rolesArrayElementSizesFuel, refArrayElementSizesFuel, hi,
              roles_isInlined_eq_abiStatic elem, hStatic,
              roles_inlinedSize_eq_abiStaticBytes elem,
              rolesArrayElementSizesFuel_eq_refArrayElementSizesFuel fuel]
          · simp [rolesArrayElementSizesFuel, refArrayElementSizesFuel, hi,
              roles_isInlined_eq_abiStatic elem, hStatic,
              rolesDynamicElementBlock_eq_refDynamicElementBlock,
              rolesEncodedSizeFuel_eq_refEncodedSizeFuel fuel,
              rolesArrayElementSizesFuel_eq_refArrayElementSizesFuel fuel]
        · simp [rolesArrayElementSizesFuel, refArrayElementSizesFuel, hi]

  theorem rolesEncodedSizeFuel_eq_refEncodedSizeFuel
      (fuel : Nat) (data : Calldata) (location : Nat) (t : AbiTy) :
      rolesEncodedSizeFuel fuel data location t =
        refEncodedSizeFuel fuel data location t := by
    cases fuel with
    | zero => simp [rolesEncodedSizeFuel, refEncodedSizeFuel]
    | succ fuel =>
        cases t with
        | staticWords n => simp [rolesEncodedSizeFuel, refEncodedSizeFuel]
        | dynamicBytes => simp [rolesEncodedSizeFuel, refEncodedSizeFuel]
        | string => simp [rolesEncodedSizeFuel, refEncodedSizeFuel]
        | tuple children =>
            simp [rolesEncodedSizeFuel, refEncodedSizeFuel,
              rolesTupleTailSizesFuel_eq_refTupleTailSizesFuel fuel]
        | dynamicArray elem =>
            simp [rolesEncodedSizeFuel, refEncodedSizeFuel,
              rolesArrayElementSizesFuel_eq_refArrayElementSizesFuel fuel]
        | abiEncoded inner => simp [rolesEncodedSizeFuel, refEncodedSizeFuel]
        | transparent child =>
            simp [rolesEncodedSizeFuel, refEncodedSizeFuel,
              rolesEncodedSizeFuel_eq_refEncodedSizeFuel fuel]
end

theorem rolesValueRegion_eq_refValueRegion
    (data : Calldata) (location : Nat) (t : AbiTy) :
    rolesValueRegion data location t = refValueRegion data location t := by
  simp [rolesValueRegion, refValueRegion,
    rolesEncodedSizeFuel_eq_refEncodedSizeFuel]

theorem rolesLeafRegionFuel_eq_refLeafRegionFuel
    (fuel : Nat) (data : Calldata) (location : Nat) (t : AbiTy)
    (path : List Nat) :
    rolesLeafRegionFuel fuel data location t path =
      refLeafRegionFuel fuel data location t path := by
  induction fuel generalizing location t path with
  | zero =>
      simp [rolesLeafRegionFuel, refLeafRegionFuel]
  | succ fuel ih =>
      cases path with
      | nil =>
          simp [rolesLeafRegionFuel, refLeafRegionFuel,
            rolesValueRegion_eq_refValueRegion]
      | cons i rest =>
          cases t with
          | staticWords n =>
              simp [rolesLeafRegionFuel, refLeafRegionFuel]
          | dynamicBytes =>
              simp [rolesLeafRegionFuel, refLeafRegionFuel]
          | string =>
              simp [rolesLeafRegionFuel, refLeafRegionFuel]
          | tuple children =>
              simp [rolesLeafRegionFuel, refLeafRegionFuel,
                rolesChildBlock_eq_refTupleChildBlock, ih]
          | dynamicArray elem =>
              by_cases hStatic : abiStatic elem = true
              · simp [rolesLeafRegionFuel, refLeafRegionFuel,
                  roles_isInlined_eq_abiStatic elem, hStatic,
                  roles_inlinedSize_eq_abiStaticBytes elem, ih]
              · simp [rolesLeafRegionFuel, refLeafRegionFuel,
                  roles_isInlined_eq_abiStatic elem, hStatic,
                  safeTailFromHead_eq_canonicalTailStart,
                  refDynamicElementBlock, ih]
          | abiEncoded inner =>
              simp [rolesLeafRegionFuel, refLeafRegionFuel, ih]
          | transparent child =>
              simp [rolesLeafRegionFuel, refLeafRegionFuel, ih]

theorem roles_decoder_faithful
    (data : Calldata) (t : AbiTy) (path : List Nat) :
    roles_ref_faithful_spec data t path := by
  unfold roles_ref_faithful_spec rolesTopLevelLeafRegion refTopLevelLeafRegion
  exact rolesLeafRegionFuel_eq_refLeafRegionFuel (decoderFuel t path) data
    selectorSize t path

theorem bounds_safe_dynamicPayloadRegion
    (data : Calldata) (location : Nat) :
    bounds_safe_result data (dynamicPayloadRegion data location) := by
  unfold dynamicPayloadRegion bounds_safe_result
  cases h : guardedWord data location with
  | none => simp
  | some n =>
      by_cases hb : inBounds data { start := location, size := wordSize + ceil32 n } = true
      · simp [hb]
      · simp [hb]

theorem bounds_safe_rolesValueRegion
    (data : Calldata) (location : Nat) (t : AbiTy) :
    bounds_safe_result data (rolesValueRegion data location t) := by
  unfold rolesValueRegion bounds_safe_result
  cases hSize : rolesEncodedSizeFuel (decoderValueFuel t) data location t with
  | overflow => simp [hSize]
  | ok r =>
      by_cases hb : inBounds data { start := location, size := r.size } = true
      · simp [hSize, hb]
      · simp [hSize, hb]

theorem bounds_safe_rolesLeafRegionFuel
    (fuel : Nat) (data : Calldata) (location : Nat) (t : AbiTy)
    (path : List Nat) :
    bounds_safe_result data (rolesLeafRegionFuel fuel data location t path) := by
  induction fuel generalizing location t path with
  | zero =>
      simp [rolesLeafRegionFuel, bounds_safe_result]
  | succ fuel ih =>
      cases path with
      | nil =>
          simp [rolesLeafRegionFuel]
          exact bounds_safe_rolesValueRegion data location t
      | cons i rest =>
          cases t with
          | staticWords n =>
              simp [rolesLeafRegionFuel, bounds_safe_result]
          | dynamicBytes =>
              simp [rolesLeafRegionFuel, bounds_safe_result]
          | string =>
              simp [rolesLeafRegionFuel, bounds_safe_result]
          | tuple children =>
              unfold rolesLeafRegionFuel
              cases h : rolesChildBlock data location children i with
              | none => simp [h, bounds_safe_result]
              | some pair =>
                  rcases pair with ⟨child, childLocation⟩
                  simp [h]
                  exact ih childLocation child rest
          | dynamicArray elem =>
              unfold rolesLeafRegionFuel
              cases hWord : guardedWord data location with
              | none => simp [bounds_safe_result]
              | some count =>
                  by_cases hi : i < count
                  · by_cases hInline : rolesIsInlined elem = true
                    · simp [hi, hInline]
                      exact ih (location + wordSize + i * rolesInlinedSize elem) elem rest
                    · simp [hi, hInline]
                      cases hTail : safeTailFromHead data (location + wordSize) (i * wordSize) with
                      | none => simp [bounds_safe_result]
                      | some childLocation =>
                          simp
                          exact ih childLocation elem rest
                  · simp [hi, bounds_safe_result]
          | abiEncoded inner =>
              unfold rolesLeafRegionFuel
              cases hWord : guardedWord data location with
              | none => simp [bounds_safe_result]
              | some n =>
                  simp
                  exact ih (location + wordSize) inner (i :: rest)
          | transparent child =>
              unfold rolesLeafRegionFuel
              exact ih location child (i :: rest)

theorem roles_decoder_bounds_safe
    (data : Calldata) (t : AbiTy) (path : List Nat) :
    roles_bounds_safe_spec data t path := by
  unfold roles_bounds_safe_spec rolesTopLevelLeafRegion
  exact bounds_safe_rolesLeafRegionFuel (decoderFuel t path) data selectorSize t path

theorem canonical_injectivity
    (data₁ data₂ : Calldata) (t : AbiTy) (path : List Nat) :
    canonical_injectivity_spec data₁ data₂ t path := by
  intro h₁ h₂ hRef
  unfold governed_field_agreement
  unfold roles_ref_faithful_spec at h₁ h₂
  rw [h₁, h₂]
  exact hRef

end Benchmark.Cases.Zodiac.RolesDecoderFaithfulness
