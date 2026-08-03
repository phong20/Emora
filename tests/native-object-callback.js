function onMessage(message) {
  console.log(message);
}

const handlers = {
  message: onMessage
};

handlers.message("payload");
