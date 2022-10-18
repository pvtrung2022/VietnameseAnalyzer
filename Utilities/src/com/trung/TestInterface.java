package com.trung;

import java.util.ArrayList;
import java.util.HashSet;

@FunctionalInterface
public interface TestInterface<S,T>
{
    public T apply(S[] a);
}
