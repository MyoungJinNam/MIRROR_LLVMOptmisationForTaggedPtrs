# README #

1. Create a folder/clone a repo under LLVM SRC (e.g. under /lib/Transforms). 
2. Add the folloiwing line to CMakeLists.txt in a parent folder:
" add_subdirectory(RemoveRTChks)"
3. Build
4. If successfully built, it will create RMRTChks_SelfContained.so under /BUILD_DIR/lib/
5. How to instrument:
"
$CLANG \
$OPTISATION_LEVEL \
-flto \
-fuse-ld=gold \
-Xclang -load -Xclang "/PATH/TO/TAGUPDATE_LIB_FILE"  \
-Xclang -load -Xclang "/PATH/TO/UNTAG_LIB_FILE"  \
-Xclang -load -Xclang "/PATH/TO/RMCHKS_LIB_FILE/"  \
-include "/PATH/TO/HOOK_HEADER" \
$WRAP_LIST "/PATH/TO/WRAPPERS_OBJ_FILE" \
-Xlinker "/PATH/TO/HOOK_FUNC_OBJ_FILE" \
-lm \
"${TESTSRC_1}" "${TESTSRC_2}" "${TESTSRC_3}" "${TESTSRC_4}" \
-o example 
"
