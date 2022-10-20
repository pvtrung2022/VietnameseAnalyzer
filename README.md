Dự án này được dùng để phân tích cấu trúc câu tiếng Việt một cách tự động.

Dự án GitHub này bao gồm hai dự án IntelliJ IDEA là VietnameseAnalyzer và Utilities trong các thư mục tương ứng. Dự án thứ nhất là dự án chính và tham chiếu đến dự án thứ hai. Trong quá trình thực hiện dự án có sử dụng jlink của Mathematica để tham chiếu nên khi sử dụng bạn cần phải tham chiếu đến thư viện JLink.jar để tránh báo lỗi. Thực tế thì bạn không cần phải biết cách sử dụng thư viện này bởi vì các hàm chính để chạy chương trình không tham chiếu đến thư viện này.

Để chạy chương trình đầu tiên bạn sẽ gọi VietnameseAnalyzer.initialize() để chương trình tải những thông tin cần thiết vào các biến tĩnh. Sau đó gọi Vietnamese.decideParser(sentence) với sentence là câu bất kỳ bạn nhập vào sẽ cho ra cấu trúc ngữ pháp phụ thuộc của câu (Dependency grammar) dưới dạng một đối tượng đồ thị (Graph) được thiết lập trong dự án Utilities. Vì hàm tĩnh VietnameseAnalyzer.initialize() tải các thông tin cần thiết vào các biến tĩnh nên bạn chỉ cần gọi một lần trong suốt quá trình hoạt động của Java. Để cụ thể hơn bạn vui lòng chạy chương trình trong file Test.java trong dự án VietnameseAnalyzer của IntelliJ IDEA

Dự án này được thực hiện trên IntelliJ IDEA 2022.2.3 và Java 11.0.15
