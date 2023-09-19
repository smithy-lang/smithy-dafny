package software.amazon.polymorph.smithypython;

public class Constants {

  // Dafny ApplicationProtocol constants
  public static String DAFNY_APPLICATION_PROTOCOL_NAME = "dafny";
  public static String DAFNY_PROTOCOL_PYTHON_FILENAME = ".dafny_protocol";
  public static String DAFNY_PROTOCOL_REQUEST = "DafnyRequest";
  public static String DAFNY_PROTOCOL_RESPONSE = "DafnyResponse";

  // Polymorph settings
  public enum GenerationType {
    LOCAL_SERVICE,
    WRAPPED_LOCAL_SERVICE_TEST,
    AWS_SDK;



    @Override
    public String toString() {
      return switch (this) {
        case LOCAL_SERVICE -> "LocalService";
        case WRAPPED_LOCAL_SERVICE_TEST -> "WrappedLocalServiceTest";
        case AWS_SDK -> "AwsSdk";
      };
    }
  }

}
