package vietnameseanalyze;

import java.io.Serializable;
import java.util.HashSet;

public class CustomHashSet<T> extends HashSet<T>
{
    public CustomHashSet(T[] eles)
    {
        super();
        for (var ele : eles)
            this.add(ele);
    }
}
