get_filename_component(TARGET_NAME "${CMAKE_CURRENT_SOURCE_DIR}" NAME)

set(TARGET_NAME "sat-solver")

file(GLOB SOURCES_LIST
    "${CMAKE_CURRENT_SOURCE_DIR}/source/*.cpp"
    "${CMAKE_CURRENT_SOURCE_DIR}/include/*.cpp")
file(GLOB HEADERS_LIST
    "${CMAKE_CURRENT_SOURCE_DIR}/include/*.h")
set(INCLUDE_DIRS
    "${CMAKE_CURRENT_SOURCE_DIR}/include/")

# 新增可執行檔目標
add_executable(${TARGET_NAME} 
    "${SOURCES_LIST}" 
    "${HEADERS_LIST}")

# 新增標頭檔目錄
target_include_directories(${TARGET_NAME} 
    PRIVATE "${INCLUDE_DIRS}")

# 新增連接器選項
target_link_options(${TARGET_NAME} 
    PRIVATE "$<$<CXX_COMPILER_ID:MSVC>:/STACK:4000000>"
    # PRIVATE "$<$<CXX_COMPILER_ID:GNU>:--stack,2000000>"
    )

# get_filename_component(TARGET_NAME "${CMAKE_CURRENT_SOURCE_DIR}" NAME)
# aux_source_directory("./src" SOURCES)
# add_executable(${TARGET_NAME} ${SOURCES})
# target_include_directories(${TARGET_NAME} PRIVATE "./src")
# target_link_options(${TARGET_NAME} 
#     PRIVATE "$<$<CXX_COMPILER_ID:MSVC>:/STACK:2000000>"
#     # PRIVATE "$<$<CXX_COMPILER_ID:GNU>:--stack=2000000>"
# )