cmake_minimum_required(VERSION 3.8)
project(Final-Project-Sudoku LANGUAGES CXX C)
message(STATUS "----- ${PROJECT_NAME}")

# Set the output directory
set(MY_OUTPUT_DIR "${CMAKE_CURRENT_BINARY_DIR}/out")
set(MY_OUTPUT_BIN_DIR "${MY_OUTPUT_DIR}/bin")
set(MY_OUTPUT_LIB_DIR "${MY_OUTPUT_DIR}/lib")
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY "$<1:${MY_OUTPUT_BIN_DIR}>")
set(CMAKE_ARCHIVE_OUTPUT_DIRECTORY "$<1:${MY_OUTPUT_LIB_DIR}>")

set(CMAKE_CXX_STANDARD 17)

if(MSVC)
    add_compile_options("/source-charset:utf-8")
    # add_link_options("/STACK:2000000")
elseif(GCC)
    add_compile_options("-finput-charset=utf-8")
endif()

# file(GLOB_RECURSE BENCHMARKS "${CMAKE_CURRENT_SOURCE_DIR}/benchmark/*")
# file(COPY ${BENCHMARKS} DESTINATION "${MY_OUTPUT_BIN_DIR}/benchmark")

file(COPY "${CMAKE_CURRENT_SOURCE_DIR}/benchmark" 
     DESTINATION "${MY_OUTPUT_BIN_DIR}")

add_subdirectory("./source")
