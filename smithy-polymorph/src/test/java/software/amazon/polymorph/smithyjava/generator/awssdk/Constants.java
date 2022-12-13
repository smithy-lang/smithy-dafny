package software.amazon.polymorph.smithyjava.generator.awssdk;

public class Constants {
    static String DoSomethingOperation = """
              @Override
              public Result<DoSomethingResponse, Error> DoSomething(DoSomethingRequest input) {
                com.amazonaws.services.kms.model.DoSomethingRequest converted = ToNative.DoSomethingRequest(input);
                try {
                  DoSomethingResult result = _impl.doSomething(converted);
                  DoSomethingResponse dafnyResponse = ToDafny.DoSomethingResponse(result);
                  return Result.create_Success(dafnyResponse);
                } catch (DependencyTimeoutException ex) {
                  return Result.create_Failure(ToDafny.Error(ex));
                } catch (AWSKMSException ex) {
                  return Result.create_Failure(ToDafny.Error(ex));
                }
              }
            """;

    static String DoVoidOperation = """
              @Override
              public Result<Tuple0, Error> DoVoid(DoVoidRequest input) {
                com.amazonaws.services.kms.model.DoVoidRequest converted = ToNative.DoVoidRequest(input);
                try {
                  _impl.doVoid(converted);
                  return Result.create_Success(Tuple0.create());
                } catch (DependencyTimeoutException ex) {
                  return Result.create_Failure(ToDafny.Error(ex));
                } catch (AWSKMSException ex) {
                  return Result.create_Failure(ToDafny.Error(ex));
                }
              }
            """;

    static String MockKmsShim = """
            package Dafny.Com.Amazonaws.Kms;
            
            import Dafny.Com.Amazonaws.Kms.Types.DoSomethingRequest;
            import Dafny.Com.Amazonaws.Kms.Types.DoSomethingResponse;
            import Dafny.Com.Amazonaws.Kms.Types.DoVoidRequest;
            import Dafny.Com.Amazonaws.Kms.Types.Error;
            import Dafny.Com.Amazonaws.Kms.Types.IKeyManagementServiceClient;
            
            import Wrappers_Compile.Result;
            
            import com.amazonaws.services.kms.AWSKMS;
            import com.amazonaws.services.kms.model.AWSKMSException;
            import com.amazonaws.services.kms.model.DependencyTimeoutException;
            import com.amazonaws.services.kms.model.DoSomethingResult;
            import dafny.Tuple0;
            
            import java.lang.Override;
            import java.lang.String;
            
            public class Shim implements IKeyManagementServiceClient {
              private final AWSKMS _impl;
              
              private final String region;
              
              public Shim(final AWSKMS impl, final String region) {
                this._impl = impl;
                this.region = region;
              }
              
              public String region() {
                return this.region;
              }
              
              %s
              %s
            }
            """.formatted(DoSomethingOperation, DoVoidOperation);

}
