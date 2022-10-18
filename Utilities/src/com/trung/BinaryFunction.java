package com.trung;

@FunctionalInterface
public interface BinaryFunction<S,T,Q>
{
    public Q apply(S s,T t);
}
