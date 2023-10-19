package software.amazon.polymorph.smithypython.localservice;

import software.amazon.polymorph.smithypython.common.Constants;
import software.amazon.smithy.python.codegen.PythonWriter;
import software.amazon.smithy.python.codegen.sections.SendRequestSection;
import software.amazon.smithy.utils.CodeInterceptor.Appender;

/**
 * Dafny plugin's interceptor for SendRequestSection.
 * By default, Smithy-Python will generate code to make an HTTP request in this section.
 * Dafny plugin overrides this to interact with DafnyImplInterface.
 * Since the Appender interface doesn't implement a mechanism to pass in GenerationContext,
 *   we cannot use the Smithy model to decide how to write this section,
 *   and this section must be written as static (unchanging) code.
 * To work around this, this section interfaces with the static DafnyImplInterface,
 *   which contains internal logic that *can* access the Smithy model.
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
                    InterceptorContext[Input, None, $L, $L], context
                )
                                
                context_with_response._transport_response = config.dafnyImplInterface.handle_request(
                    input=context_with_response.transport_request
                )
        """,
        Constants.DAFNY_PROTOCOL_REQUEST,
        Constants.DAFNY_PROTOCOL_RESPONSE);
  }
}