// Code generated by depstubber. DO NOT EDIT.
// This is a simple stub for go-micro.dev/v4/server, strictly for use in testing.

// See the LICENSE file for information about the licensing of the original library.
// Source: go-micro.dev/v4/server (exports: Server; functions: Handle)

// Package server is a stub of go-micro.dev/v4/server, generated by depstubber.
package server

import (
	context "context"
	tls "crypto/tls"
	time "time"
)

func Handle(_ Handler) error {
	return nil
}

type Handler interface {
	Endpoints() []interface{}
	Handler() interface{}
	Name() string
	Options() HandlerOptions
}

type HandlerFunc func(context.Context, Request, interface{}) error

type HandlerOption func(*HandlerOptions)

type HandlerOptions struct {
	Metadata map[string]map[string]string
	Internal bool
}

type HandlerWrapper func(HandlerFunc) HandlerFunc

type Message interface {
	Body() []byte
	Codec() interface{}
	ContentType() string
	Header() map[string]string
	Payload() interface{}
	Topic() string
}

type Option func(*Options)

type Options struct {
	Logger           interface{}
	Broker           interface{}
	Registry         interface{}
	Tracer           interface{}
	Transport        interface{}
	Context          context.Context
	Router           Router
	RegisterCheck    func(context.Context) error
	Metadata         map[string]string
	TLSConfig        *tls.Config
	Codecs           map[string]interface{}
	Name             string
	Id               string
	Version          string
	Advertise        string
	Address          string
	HdlrWrappers     []HandlerWrapper
	ListenOptions    []interface{}
	SubWrappers      []SubscriberWrapper
	RegisterInterval time.Duration
	RegisterTTL      time.Duration
}

type Request interface {
	Body() interface{}
	Codec() interface{}
	ContentType() string
	Endpoint() string
	Header() map[string]string
	Method() string
	Read() ([]byte, error)
	Service() string
	Stream() bool
}

type Response interface {
	Codec() interface{}
	Write(_ []byte) error
	WriteHeader(_ map[string]string)
}

type Router interface {
	ProcessMessage(_ context.Context, _ Message) error
	ServeRequest(_ context.Context, _ Request, _ Response) error
}

type Server interface {
	Handle(_ Handler) error
	Init(_ ...Option) error
	NewHandler(_ interface{}, _ ...HandlerOption) Handler
	NewSubscriber(_ string, _ interface{}, _ ...SubscriberOption) Subscriber
	Options() Options
	Start() error
	Stop() error
	String() string
	Subscribe(_ Subscriber) error
}

type Subscriber interface {
	Endpoints() []interface{}
	Options() SubscriberOptions
	Subscriber() interface{}
	Topic() string
}

type SubscriberFunc func(context.Context, Message) error

type SubscriberOption func(*SubscriberOptions)

type SubscriberOptions struct {
	Context  context.Context
	Queue    string
	AutoAck  bool
	Internal bool
}

type SubscriberWrapper func(SubscriberFunc) SubscriberFunc
