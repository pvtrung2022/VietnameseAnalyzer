package com.trung;

@FunctionalInterface
public interface BinaryAction<S,T>
{
    public void apply(S s,T t);
}
