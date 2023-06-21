package software.amazon.smithy.dafny.python;

import software.amazon.smithy.python.codegen.PythonWriter;
import software.amazon.smithy.python.codegen.sections.SendRequestSection;
import software.amazon.smithy.utils.CodeInterceptor.Appender;

/**
 * Dafny plugin's interceptor for SendRequestSection.
 * By default, Smithy-Python will generate code to make an HTTP request.
 * Dafny plugin overrides this to interact with DafnyImplInterface.
 */
final class SendRequestInterceptor implements
    Appender<SendRequestSection, PythonWriter> {
  @Override
  public Class<SendRequestSection> sectionType() {
    return SendRequestSection.class;
  }

  @Override
  public void append(PythonWriter writer, SendRequestSection section) {
    writer.write("""
                # Step 7m: Invoke http_client.send
                if config.dafnyImplInterface.impl is None:
                    raise Exception("No impl found on the operation config.")
                
                context_with_response = cast(
                    InterceptorContext[Input, None, DafnyRequest, DafnyResponse], context
                )
                
                print(f"transport_request is {context_with_response.transport_request}")
                
                context_with_response._transport_response = config.dafnyImplInterface.handle_request(
                    input=context_with_response.transport_request
                )
        """);
  }
}
