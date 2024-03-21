cmake_minimum_required(VERSION 3.0)
project(AtomicSharedPtr)
add_executable(AtomicSharedPtr main.cpp)

target_compile_features(AtomicSharedPtr INTERFACE cxx_std_20)
