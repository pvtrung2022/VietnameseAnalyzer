package vietnameseanalyzer;

import com.trung.*;

public class Test
{
    public static void main(String[] argv)
    {
        VietnameseAnalyzer.initialize();
        System.out.println("finished initialization");
        var sentence="tôi yêu cô ấy rất nhiều";
        var parser=VietnameseAnalyzer.decideParser(sentence);
        System.out.println(parser);
    }
}
