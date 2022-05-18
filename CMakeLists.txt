add_llvm_library( RMRTChks_SelfContained MODULE #BUILDTREE_ONLY
  RemoveRTChks.cpp 

  DEPENDS
  intrinsics_gen
  PLUGIN_TOOL
  opt
  )
