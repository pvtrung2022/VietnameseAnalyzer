package vietnameseanalyzer;

import com.trung.*;

public class Test
{
    /**
     * x&amp; &lt;  y
     */
    public static NullFunction<String> foo = () ->
    {
        // getStackTrace() method return current
        // method name at 0th index

//        NullFunction<String> func = () ->
//        {
//            return new Exception()
//                    .getStackTrace()[0]
//                    .getMethodName();
//        };
        String nameofCurrMethod = new Exception()
                .getStackTrace()[0]
                .getMethodName();
        return nameofCurrMethod;
    };

    public static void main(String[] argv)
    {
        VietnameseAnalyzer.initialize();
        VietnameseAnalyzer.getErrorAppearanceStatics();
        System.out.println("here is the main step");
        var sentence="người, tôi yêu, xinh đẹp, giờ đã yêu người khác rồi";
//        var jg=VietnameseAnalyze.makeAnalyzingGraph(sentence);
        var parser=VietnameseAnalyzer.decideParser(sentence);
        System.out.println(parser);
//        var root=Utilities.firstCase(jg.vertexList(),x->x.Word.equals("có"));
//        var maxTree=VietnameseAnalyze.decideParser(jg);
//        System.out.println(maxTree);

//        var wordInfos = new String[][]{
//                {"tôi", "N"},
//                {"yêu","V"},
//                {"cô","N"}
//        };
//        var res = VietnameseAnalyzer.decideParser(wordInfos);
//        System.out.println(res);

//        var sentence="tôi có người ?";
//        var res=VietnameseAnalyze.analyzeSentence(sentence);
//        System.out.println(res);
    }
}
