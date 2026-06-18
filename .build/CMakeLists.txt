cmake_minimum_required(VERSION 3.10)

project(LambdaInterpreter C CXX)

# Option for instrumentation using the tracy profiler
option(TRACY "Enable Tracy profiler" OFF)

# Directories and executable
set(SRC_DIR "${CMAKE_CURRENT_SOURCE_DIR}/..")
set(DEP_DIR "${SRC_DIR}/dep")

add_executable(lambda ${SRC_DIR}/main.c)

# Sets include directories
target_include_directories(lambda PRIVATE "${DEP_DIR}")

# Compilation and linking flags with link time optimization
if(CMAKE_C_COMPILER_ID MATCHES "^(GNU|Clang)$")
    target_compile_options(lambda PRIVATE
        -Wall -Wextra -pedantic
        -Wconversion -Wdouble-promotion
        -Wno-parentheses -Wno-sign-conversion
        "$<$<CONFIG:Release>:-O2>"
    )

    target_link_options(lambda PRIVATE
        "$<$<C_COMPILER_ID:Clang>:-fuse-ld=lld>"
        "$<$<CONFIG:Release>:-s>"
        "$<$<CONFIG:MinSizeRel>:-s>"
    )

elseif(MSVC)
    target_compile_options(lambda PRIVATE
        /W4 /wd4146 /wd4245 /wd4456 /permissive- /D_CRT_SECURE_NO_WARNINGS
    )

    add_link_options("/Manifest:No")
endif()

if(CMAKE_C_COMPILER_ID MATCHES "^(GNU|Clang|MSVC)$")
    # Builds with the tracy profiler
    if(TRACY)        
        target_sources(lambda PRIVATE
            ${DEP_DIR}/tracy/public/TracyClient.cpp
        )

        set_source_files_properties(
            "${DEP_DIR}/tracy/public/TracyClient.cpp"
            PROPERTIES COMPILE_OPTIONS "$<$<C_COMPILER_ID:MSVC>:/W0>;$<$<NOT:$<C_COMPILER_ID:MSVC>>:-w>"
        )

        target_compile_options(lambda PRIVATE
            "$<$<NOT:$<C_COMPILER_ID:MSVC>>:-fno-omit-frame-pointer>"
            "$<$<C_COMPILER_ID:MSVC>:/Oy->"
        )

        target_compile_definitions(lambda PRIVATE
            TRACY_ENABLE
            TRACY_NO_EXIT
        )

        target_link_libraries(lambda PRIVATE
            "$<$<PLATFORM_ID:Windows>:dbghelp>"
            "$<$<PLATFORM_ID:Windows>:secur32>"
            "$<$<PLATFORM_ID:Windows>:ws2_32>"
        )
    endif()

    # Assembles a c file into assembly with source code
    if (DEFINED ASSEMBLY_FILE AND MSVC)
        set_source_files_properties(
            "${SRC_DIR}/${ASSEMBLY_FILE}.c"
            PROPERTIES COMPILE_OPTIONS "/FAs;/Fa$<TARGET_FILE_DIR:lambda>/${ASSEMBLY_FILE}.s"
        )

        add_custom_target(asm DEPENDS lambda)
    else()
        # Enables link time optimization
        set_property(TARGET lambda PROPERTY INTERPROCEDURAL_OPTIMIZATION TRUE)
        set_property(TARGET lambda PROPERTY INTERPROCEDURAL_OPTIMIZATION_DEBUG FALSE)
    endif()
        
    if (DEFINED ASSEMBLY_FILE AND NOT MSVC)
        set(COMPILE_FLAGS "$<$<CONFIG:Release>:-O2>" -isystem ${DEP_DIR})
        if (${TRACY})
            list(APPEND COMPILE_FLAGS -fno-omit-frame-pointer -DTRACY_ENABLE -DTRACY_NO_EXIT)
        endif()

        add_custom_command(
            OUTPUT "${CMAKE_BINARY_DIR}/${ASSEMBLY_FILE}.s"
            COMMAND
                ${CMAKE_C_COMPILER} ${COMPILE_FLAGS}
                -fno-lto -S -masm=intel -fverbose-asm
                ${SRC_DIR}/${ASSEMBLY_FILE}.c
                -o ${CMAKE_BINARY_DIR}/${ASSEMBLY_FILE}.s
            DEPENDS "${SRC_DIR}/${ASSEMBLY_FILE}.c"
        )

        add_custom_target(asm DEPENDS "${CMAKE_BINARY_DIR}/${ASSEMBLY_FILE}.s")
    endif()
endif()
